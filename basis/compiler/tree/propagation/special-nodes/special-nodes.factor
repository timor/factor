USING: accessors arrays classes.algebra classes.tuple classes.tuple.private
combinators.short-circuit compiler.tree compiler.tree.propagation.info kernel
kernel.private
sequences sets slots.private words ;

IN: compiler.tree.propagation.special-nodes


! * Predicate hierarchy for node dispatch
PREDICATE: flushable-call < #call word>> flushable? ;
PREDICATE: slot-call < flushable-call word>> \ slot eq? ;
PREDICATE: literal-slot-call < slot-call
    in-d>> second value-info { [ literal?>> ] [ literal>> 0 = not ] } 1&& ; ! Exclude length slot calls

PREDICATE: rw-slot-call < literal-slot-call
    in-d>> first2 [ value-info class>> ] [ value-info literal>> ] bi* swap read-only-slot? not ;
PREDICATE: tuple-boa-call < flushable-call word>> \ <tuple-boa> eq? ;

PREDICATE: non-flushable-call < #call flushable-call? not ;
PREDICATE: resize-array-call < non-flushable-call word>> \ resize-array eq? ;
PREDICATE: inlined-call < non-flushable-call body>> >boolean ;
! TODO: check the other primitives, clone sans (clone) etc...
! PREDICATE: safe-primitive-call < non-flushable-call word>>
!     { resize-array } in? ;
UNION: safe-primitive-call resize-array-call ;
UNION: local-allocating-call flushable-call safe-primitive-call ;
! PREDICATE: non-inlined-call < non-flushable-call inlined-call? not ;
! PREDICATE: known-safe-call < non-inlined-call word>> { resize-array } in? ;
UNION: non-escaping-call flushable-call inlined-call safe-primitive-call ;

PREDICATE: set-slot-call < non-flushable-call word>> \ set-slot eq? ;
PREDICATE: literal-set-slot-call < set-slot-call in-d>> third value-info literal?>> ;
PREDICATE: tuple-set-slot-call < literal-set-slot-call in-d>> second value-info class>> tuple class<= ;
PREDICATE: sequence-set-slot-call < literal-set-slot-call in-d>> second
    value-info class>> fixed-length class<= ;
PREDICATE: box-set-slot-call < sequence-set-slot-call in-d>> second value-info
    slots>> dup [ ?first dup [ literal>> 1 = ] when ] when ;

PREDICATE: tuple-push < #push literal>> tuple? ;
PREDICATE: mutable-tuple-push < tuple-push literal>> immutable-tuple-class? not ;
PREDICATE: sequence-push < #push literal>> fixed-length? ;
