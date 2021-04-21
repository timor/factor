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
M: rw-slot-call propagate-slot-refs
    ! [ call-next-method ] keep
    propagate-rw-slots? [
        [ in-d>> second value-info literal>> ]
        [ in-d>> first value-info
          [ 1 - ] [ slots>> ] bi* ?nth
        ]
        [ out-d>> first
          over [ refine-value-info ] [ 2drop ] if
        ] tri
    ] [ drop ] if ;

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
M: #call propagate-escape
    [ in-d>> call-values-escape ]
    [ out-d>> call-values-escape ] bi ;
