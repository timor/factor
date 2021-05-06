USING: accessors classes classes.tuple.private combinators
combinators.short-circuit compiler.tree compiler.tree.propagation.copy
compiler.tree.propagation.escaping compiler.tree.propagation.info
compiler.tree.propagation.nodes compiler.tree.propagation.special-nodes kernel
math sequences sets sets.extras ;

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

: summary-slot-access ( #call -- info )
    in-d>> first value-info summary-slot>>
    [ lazy-info check-instance lazy-info>info ] [ pointer-info ] if* ;

M: rw-tuple-slot-call propagate-slot-call*
    strong-slot-access ;

M: ro-slot-call propagate-slot-call*
    strong-slot-access ;

M: box-rw-slot-call propagate-slot-call*
    summary-slot-access ;

: slot-access-union ( slots -- info )
    [ pointer-info ]
    [ [ ] [ union-lazy-slot ] map-reduce lazy-info>info ] if-empty ;

! Known that we don't access the length slot
M: sequence-rw-slot-call propagate-slot-call*
    summary-slot-access ;

! Could be anything. Include everything we know
M: slot-call propagate-slot-call*
    in-d>> first value-info
    [ slots>> slot-access-union ]
    [ summary-slot>> [ lazy-info>info ] [ pointer-info ] if* ] bi
    value-info-union ;

! NOTE: we check literal>> instead of literal?>>, because
! pseudo-deliteralization keeps the literal slot.
: propagate-slot-call ( #call -- info )
    dup in-d>> first value-info literal>>
    [ layout-up-to-date? ] [ t ] if*
    [ propagate-slot-call* ]
    [ drop pointer-info ] if ;

M: slot-call propagate-before
    propagate-rw-slots? [
        [ propagate-slot-call ]
        [ over [ out-d>> first set-value-info ] [ 2drop ] if ] bi
    ]
    [ call-next-method ] if ;
