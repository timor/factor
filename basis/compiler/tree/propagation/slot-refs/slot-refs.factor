USING: accessors combinators combinators.short-circuit compiler.tree
compiler.tree.propagation.escaping compiler.tree.propagation.info
compiler.tree.propagation.nodes compiler.tree.propagation.reflinks kernel math
sequences sets ;

IN: compiler.tree.propagation.slot-refs

! Find ourselves in other tuples slots.
! Return whether we are still referenced, and check for a strong definition
! relation by checking whether our slot-refs are a superset of the target.  If
! not, other definitions have been involved, thus only weak update is possible.

: back-ref-slot ( info slot-ref -- strong? current? )
    [ slot-refs>> ] [ dereference slot-refs>> ] bi*
    [ swap subset? ] [ intersects? ] 2bi ; inline
    ! dup dereference slot-refs>>
    ! [ in? ]
    ! [ length 1 = ] bi swap ;

! Check if this value has been defined by something that could have escaped
! and modified.
: value-info-escapes? ( info -- ? )
    slot-refs>> members
    {
        ! [ null? ]                 ! Unknown allocation, should not happen!
        ! proper introduce node
        [ [ input-ref? ] any? ]
        [ [ value-escapes? ] any? ] } 1|| ;


DEFER: notice-slot-changed
: notice-slot-ref-changed ( slot-ref -- )
    dup mutable? [ parent-info notice-slot-changed ] [ drop ] if ;


! Must ripple through
: notice-slot-changed ( info -- )
    dup slot-refs>> members [
        2dup back-ref-slot
        [  [ [ strong-update ]
             [ weak-update ] if ] keepd
           notice-slot-ref-changed
        ]
        [ 3drop ] if
    ] with each ;

! set-slot ( value obj n -- )
M: tuple-set-slot-call propagate-slot-refs
    in-d>> first3
    value-info literal>> register-tuple-slot-storage
    ! notice-slot-changed
    ;

M: tuple-boa-call propagate-slot-refs
    [ out-d>> first ]
    [ in-d>> but-last ] bi
    [ 2 + register-tuple-slot-storage ] with each-index ;

! TODO: check node selection semantics! ( should propbably be the same as allocation! )
M: non-escaping-call propagate-slot-refs
    drop ;

M: #call propagate-slot-refs
    out-d>> [ unknown-ref set-slot-ref ] each ;

M: #introduce propagate-slot-refs
    out-d>> [ <input-ref> set-slot-ref ] each-index ;

! ** Change value info for slot calls
! Situation: output-value-infos has run.  Now repeat.  For now, only if this is
! an rw-slot access

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
!     - info(V).slotrefs = { ..., C0.S0i, ... }
!     - info(C0) = { ..., S0i = info(V), ... }
!   - possibly higher level:
!     - some container Cx's slot Sxj MAY contain value C0 with info(C0), i.e.
!       - info(C0).slotrefs = { ..., Cx.Sxj , ... }
!       - info(Cx) = { ..., Sxj = info(C0), ... }

! Target State:
! - info(W)'.slotrefs += C0.S0i
! - info(C0)' = { ..., S0i = info(W)', ... }
! - info(Cx)' = { ..., Sxj = info(C0)', ... }


! - Procedure notifySlotChange(C0, S0i, info(W))
!   1. info(W)'.slotrefs += C0.S0i ( register W being contained in
!   2. info(C0)' = info(C0)' // { S0i = info(W)' } ( merge slot info )
!   3. toUpdate = { }
!   4. foreach slotref Cx.Sxj in info(C0).slotrefs
!      1. fetch slotInfo = info(Cx).Sxj
!      2. If C0.S0i is not member of slotInfo.slotrefs
!         1. Target location has been changed in the meantime, don't perform update
!         2. Else
!            1. If slotInfo.slotrefs = { C0.S0i } (strong update)
!               1. slotInfo' = info(C0)'.S0i
!            2. Else the target has been defined by others also (weak update)
!               1. slotInfo' += info(C0)'.S0i (union info)
!            3. toUpdate += { Cx.Sxj, slotInfo' )
!   5. foreach { Cy.Sy, info } in toUpdate
!      1. notifySlotChange(Cy, Sy, info)

! TODO: back-propagation
! set-slot ( value obj n -- )
: propagate-tuple-set-slot-infos ( #call -- )
    in-d>> first3 [ value-info ] 2dip value-info literal>> override-slot-infos ;

M: tuple-set-slot-call propagate-before
    [ call-next-method ] keep
    propagate-rw-slots?
    [ propagate-tuple-set-slot-infos ] [ drop ] if ;

! TODO: deliteralize and handle pushes

! * Escaping slot-refs

! : follow-slot-refs ( slot-ref -- seq )
!     [ dereference slots>> [ slot-refs>> members ] gather ] closure ;

! TODO: Notify escaping by:
! 1. Add +escaping+ to the slot-ref set
! 2. Set value info to object-info
! 3. Notify other containers

! Probably baaaad complexity...
: slot-ref-escapes ( slot-ref -- )
    dup value-escapes?
    [ drop ]                    ! Break recursion
    [
        {
            [ value-escapes ]
            [ dereference slots>> [ slot-refs>> members [ slot-ref-escapes ] each ] each ]
            [ object-info swap weak-update ]
            [ notice-slot-ref-changed ]
        } cleave
    ] if ;

: call-values-escape ( values -- )
    [ value-info slot-refs>> members [ slot-ref-escapes ] each ] each ;

! M: #introduce propagate-escape
!     out-d>> call-values-escape ;

! set-slot ( value obj n -- )
! M: tuple-set-slot-call propagate-escape
!     in-d>> first2 [ value-info slot-refs>> ] bi@
!     union members equate-all-values ;

! M: tuple-boa-call propagate-escape
!     [ in-d>> but-last [ value-info slot-refs>> ] gather ]
!     [ out-d>> first value-info slot-refs>> ] bi
!     append



M: non-escaping-call propagate-escape drop ;
M: #call propagate-escape drop ;
    ! [ in-d>> call-values-escape ]
    ! [ out-d>> call-values-escape ] bi ;
