USING: accessors combinators combinators.short-circuit compiler.tree
compiler.tree.propagation.escaping compiler.tree.propagation.info
compiler.tree.propagation.copy
compiler.tree.propagation.nodes compiler.tree.propagation.special-nodes kernel math
sequences sets sets.extras ;

IN: compiler.tree.propagation.slot-refs

! * Assumptions for slot calls

! - unknown class, unknown slot: output info is union of all slots
! - unknown class, known read-only slot: output info is slot info
! - tuple class, known slot: output info is slot info
! - tuple class, unknown slot: shouldn't happen!
! - sequence, length = 1: any rw slot: output info is slot info
! - sequence, length > 1: any literal rw slot: output info is union of all slot infos
!   (excluding length slots

GENERIC: propagate-slot-call* ( #call -- info/f )

! slot ( obj m -- value )
: strong-slot-access ( #call -- info )
    [ in-d>> second value-info literal>> ]
    [ in-d>> first value-info
      [ 1 - ] [ slots>> ] bi* ?nth
      [ dup lazy-info? [ lazy-info>info ] when ] [ pointer-info ] if*
    ] bi ;

M: rw-tuple-slot-call propagate-slot-call*
    strong-slot-access ;

M: ro-slot-call propagate-slot-call*
    strong-slot-access ;

M: box-rw-slot-call propagate-slot-call*
    strong-slot-access ;

: slot-access-union ( slots -- info )
    [ pointer-info ]
    [ [ ] [ union-lazy-slot ] map-reduce ] if-empty ;

M: sequence-rw-slot-call propagate-slot-call*
    in-d>> first value-info slots>> dup [ rest-slice ] when
    slot-access-union ;

M: slot-call propagate-slot-call*
    in-d>> first value-info slots>>
    slot-access-union ;

M: slot-call propagate-before
    propagate-rw-slots? [
        [ propagate-slot-call* ]
        [ over [ out-d>> first set-value-info ] [ 2drop ] if ] bi
    ]
    [ call-next-method ] if ;
