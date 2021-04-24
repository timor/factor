USING: accessors combinators combinators.short-circuit compiler.tree
compiler.tree.propagation.escaping compiler.tree.propagation.info
compiler.tree.propagation.copy
compiler.tree.propagation.nodes compiler.tree.propagation.reflinks kernel math
sequences sets sets.extras ;

IN: compiler.tree.propagation.slot-refs

: value-info-escapes? ( info -- ? )
    {
        [ origin>> limbo swap in? ]
        [ slots>> [ dup [ value-info-escapes? ] when ] any? ]
    } 1||
    ;

! slot ( obj m -- value )
: propagate-rw-slot-infos ( #call -- )
    [ in-d>> second value-info literal>> ]
    [ in-d>> first value-info
      [ 1 - ] [ slots>> ] bi* ?nth
    ]
    [ out-d>> first
      over [ refine-value-info ] [ 2drop ] if
    ] tri
    ;

M: rw-slot-call propagate-before
    [ call-next-method ] keep
    propagate-rw-slots? [
        propagate-rw-slot-infos ] [ drop ] if ;

! * Backpropagation
! The regular value info propagation handles duplicates and copies on the value
! level through copy propagation.  This allows inferring that in e.g.
! ~[ dup { array } declare ]~, the value beneath top-of-stack(TOS) will also be an
! array.

! However, the link information is lost when values are assigned to storage
! locations.  E.g. for some tuple class ~foo~, ~[ { foo } declare 42 >>a ]~, will
! result in TOS being known to be of class ~foo~, but a dereferencing operation
! with ~a>>~ will have unknown output.  This is easily fixed by updating the value
! info for the "a" slot of TOS to contain 42 after the ~42 >>a~ assignment.  This
! would also apply to a simple duplication as described above.  However, more
! complex cases are not covered by this:
! 1. Nesting a container inside another one, dereferencing it multiple times,
!    changing a slot value.  This will not reflect the changed contents of the
!    slot is accessed from one of the other dereferenced values.  This is solved
!    by attaching a slot reference (slotref) to a value when it is stored inside a
!    container.  On slot update, the list of refs containing the changed container
!    is looked up, and it's slot information updated.  Then the container is also
!    marked as changed, and its containing containers updated as well.
! 2. Letting a container escape.  This is equivalent to setting all the containers
!    slots, and their slots to unknown values.  This change must then be also be
!    propagated.
! 3. Branch return.  If a storage object is propagated via a phi node, it's slots
!    contain the union information of the merged value info states.  Example:

!    - T1.x= 42;
!    - T2.x = T1;
!    - if
!      - left branch:
!        - T2.x.x = 43
!      - right branch
!        - T3.x = 66
!        - T2.x = T3
!    - phi return
!      T2' = { x= { T1 = {x = 43}, T3 = { x = 66 } } }


! A value dererencing would result in the union of the two possibilities:
! - T2'.x.x = { 43, 66 }


! If, however, T1.x.x is subsequently changed, and then T1 or T3 later accessed,
! it depends on the taken branch whether T1 or T3 has been updated. Thus, we must
! assume that both could have been set to the new value:
! - T1'.x = { 42, 44 }
! - T3'.x = { 66, 44 }


! This case is known as a *weak update*.  If the nested tuple is the same ,i.e. T1
! = T3, then we can infer that T1'.x = 44, and T3'.x = 44 after return.  This is
! known as a *strong update*.  To decide whether we can perform a strong update,
! the list of slotrefs at the target locations has to be taken into account.  If
! the target location can only have been defined by us, then we can override the
! location.  If the target location can have also been defined by some other
! access, then we expand the value information.


! Slot write update procedure:

! - Explanations:
!   - The global value info state is just info.  Note
!     that info is a tree state.  No references exist inside it.  Duplicates are
!     explicit.  If two values change at the same time somewhere inside the tree,
!     they must be explicitly synchronized.
!   - info(Value).slotrefs is the set of storage locations which are known to MAY contain
!     Value in the current state.
! - Inputs: container C0, info, S0i, W (new value)
! - Outputs: none
! - Current State:
!   - this level: container C0's slot S0i contains value V, with info(V), i.e
!     - info(V).slotrefs = { C0.S0i }
!     - info(C0).slots = { ..., S0i = info(V), ... }
!   - possibly higher level:
!     - some container Cx.Sxj and Cy.syl slot MAY contain value C0 with info(C0), i.e.
!       - info(C0).slotrefs = { Cx.Sxj, Cy.Syl }
!       - info(Cx).slots = { ..., Sxj = info(C0), ... }
!       - info(Cy).slots = { ..., Syl = info(C0), ... }


! Target State:
! - info(W)'.slotrefs += C0.S0i
! - info(C0)' = { ..., S0i = info(W)', ... }
! - info(C0)'.slotrefs = info(C0).slotrefs = { ..., Cx.Sxj , Cy.Syl, ... }
! - info(Cx)' = { ..., Sxj = info(C0)', ... }
! - info(Cy)' = { ..., Syl = info(C0)', ... }

! - Procedure notifySlotChange(C0, S0i, info(W))
!   1. info(C0)' = info(C0)' // { S0i = info(W)' } ( merge slot info )
!   2. toUpdate = { }
!   3. foreach slotref Cx.Sxj in info(C0).slotrefs
!      1. fetch refSlotInfo = info(Cx).Sxj
!      2. If info(C0).slotrefs ∩ refSlotInfo.slotrefs
!         1. Target location has been changed in the meantime, don't perform update
!         2. Else
!            1. If info(C0).slotrefs ⊇ refSlotInfo.slotrefs = (strong update)
!               1. refSlotInfo' = info(C0)'.S0i
!            2. Else the target has been defined by others also (weak update)
!               1. refSlotInfo' += info(C0)'.S0i (union info)
!            3. toUpdate += { Cx.Sxj, refSlotInfo' )
!   4. foreach { Cy.Sy, info } in toUpdate
!      1. notifySlotChange(Cy, Sy, info)

! Actual update:
! - info(W).slotrefs += C0.S0i ( register W being contained in C0 at S0i )
! - notifySlotChange(C0, S0i, info(W))


! Example, with order of things that must happen
! - T1.x = 42 -> slotrefs(42) = T1.x
! - T2.x = T1 -> slotrefs(T1) = T2.x
! - T3.x = T2 -> slotrefs(T2) = T3.x
! - T1.x <= 43
! - Update info for T1 to one which includes the T1.x = 42->43 change:
! - Tuple Value info slot update: info(T1)' <= T1'{ x= 43 }, commit
! - T1.x is now 43
! - Update info for T2 to one which includes the T2.x = T1{ x = 42} -> T1{ x =  43} change:
! - find T2.x by slot-refs(T1)
! - find info(T1)' by info(T1)', info(T1)' = T1{ x = 43}
! - Tuple value info slot update: info(T2)' <= T2'{ x = T1'{ x = 43 } }, commit
! - Update info for T3 to one which includes the T3.x = T2{ x = T1{ x = 42} } ->
!   T2{ x = { T1 {  x = 43 } } } change:
! - find T3.x by slot-refs(T2)

SINGLETONS: strong weak ;
: slot-ref-membership ( tag-refs slot-refs -- how )
    { { [ 2dup intersects? not ] [ 2drop f ] }
      { [ 2dup superset? ] [ 2drop strong ] }
      [ 2drop weak ]
    } cond ;

! TODO: move to info?
! NOTE: different to above, we assume the update has been performed before being called
! slot-ref list
! Perform all the linked container updates, return the slot-refs
! TODO: might have to handle recursive updates here!
! tag-ref is the one we use to check for updates.
:: notify-slot-change ( slot-ref -- )
    V{ } clone :> to-update
    slot-ref container-info :> new-info
    new-info slot-refs>> :> tag-refs ! "Siblings"
    tag-refs members [ mutable? ] filter
    [| ref |
     ref dereference :> ref-slot-info
     tag-refs ref-slot-info slot-refs>> slot-ref-membership
     ! slot-ref-membership
     [ strong?
       [ new-info ref strong-update ]
       [ new-info ref weak-update ] if
       ! Notify parents
       ref container-info slot-refs>> members [ mutable? ] filter
       to-update push-all
     ] when*
    ] each
    ! Hop up and above
    to-update members [ notify-slot-change ] each ;


! Inform all other containers holding this reference that we also hold it now
: propagate-tuple-boa-slot-refs ( #call -- )
    out-d>> first value-info slots>>
    [ [ slot-refs>> members [ dup mutable? [ notify-slot-change ] [ drop ] if ]
        each ] when* ] each ;

! M: tuple-boa-call propagate-before
!     [ call-next-method ] keep
!     propagate-rw-slots?
!     [ propagate-tuple-boa-slot-refs ] [ drop ] if ;

! TODO: deliteralize and handle pushes

M: non-escaping-call propagate-escape drop ;
M: #call propagate-escape drop ;
    ! [ in-d>> call-values-escape ]
    ! [ out-d>> call-values-escape ] bi ;
