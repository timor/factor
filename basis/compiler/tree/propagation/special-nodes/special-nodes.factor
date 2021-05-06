USING: accessors arrays byte-arrays classes.algebra classes.tuple
classes.tuple.private combinators.short-circuit compiler.tree
compiler.tree.propagation.info kernel sequences slots.private strings words ;

IN: compiler.tree.propagation.special-nodes

! TODO: These dispatch on environment variables, which is not great.  Possible
! solution: Split annotation into pre- and post-annoate, so we can dispatch on
! the input info instead.  May be more efficient to not annotate by value, but
! by sequence instead?

! * Predicate hierarchy for node dispatch
PREDICATE: flushable-call < #call word>> flushable? ;
PREDICATE: slot-call < flushable-call word>> \ slot eq? ;
PREDICATE: literal-slot-call < slot-call
    in-d>> second value-info literal?>> ;
PREDICATE: rw-slot-call < literal-slot-call
    in-d>> first2 [ value-info class>> ] [ value-info literal>> ] bi* swap read-only-slot? not ;
PREDICATE: ro-slot-call < literal-slot-call
    rw-slot-call? not ;

PREDICATE: rw-tuple-slot-call < rw-slot-call
    in-d>> first value-info class>> tuple class<= ;

! class is sequence, slot is not a literal 1
PREDICATE: sequence-rw-slot-call < slot-call
    in-d>> first2 [ value-info ] bi@
    [ class>> fixed-length class<= ]
    [ { [ literal?>> ] [ literal>> 1 = ] } 1&& not ] bi* and ;

PREDICATE: string-aux-reader < sequence-rw-slot-call
    in-d>> first2 [ value-info class>> string eq? ] [ value-info literal>> 2 = ] bi* and ;

: length-slot-literal ( value -- n/f )
    value-info slots>> ?first dup
    [ [ literal?>> ] [ literal>> ] bi and ]
    when ;

PREDICATE: box-rw-slot-call < sequence-rw-slot-call
    in-d>> first length-slot-literal 1 = ;

PREDICATE: tuple-boa-call < flushable-call word>> \ <tuple-boa> eq? ;

PREDICATE: non-flushable-call < #call flushable-call? not ;
PREDICATE: resize-array-call < non-flushable-call word>> \ resize-array eq? ;
PREDICATE: resize-string-call < non-flushable-call word>> \ resize-string eq? ;
PREDICATE: resize-byte-array-call < non-flushable-call word>> \ resize-byte-array eq? ;
UNION: resize-sequence-call resize-array-call resize-string-call resize-byte-array-call ;
PREDICATE: inlined-call < non-flushable-call body>> >boolean ;
! TODO: check the other primitives, clone sans (clone) etc...
! PREDICATE: safe-primitive-call < non-flushable-call word>>
!     { resize-array } in? ;
UNION: safe-primitive-call resize-sequence-call ;
UNION: local-allocating-call flushable-call resize-sequence-call ;
! PREDICATE: non-inlined-call < non-flushable-call inlined-call? not ;
! PREDICATE: known-safe-call < non-inlined-call word>> { resize-array } in? ;
UNION: non-escaping-call flushable-call inlined-call safe-primitive-call ;

PREDICATE: set-slot-call < non-flushable-call word>> \ set-slot eq? ;
PREDICATE: literal-set-slot-call < set-slot-call in-d>> third value-info literal?>> ;
PREDICATE: tuple-set-slot-call < literal-set-slot-call in-d>> second value-info class>> tuple class<= ;
PREDICATE: sequence-set-slot-call < literal-set-slot-call in-d>> second
    value-info class>> fixed-length class<= ;
PREDICATE: string-aux-writer < sequence-set-slot-call
    in-d>> { [ second value-info class>> string eq? ] [ third value-info literal>> 2 = ] } 1&& ;
PREDICATE: box-set-slot-call < sequence-set-slot-call
    in-d>> second length-slot-literal 1 = ;
PREDICATE: non-literal-sequence-set-slot-call < set-slot-call
    { [ literal-set-slot-call? not ] [ in-d>> second value-info class>>
                                       fixed-length class<= ] } 1&& ;

PREDICATE: tuple-push < #push literal>> tuple? ;
PREDICATE: mutable-tuple-push < tuple-push literal>> immutable-tuple-class? not ;
PREDICATE: sequence-push < #push literal>> fixed-length? ;
