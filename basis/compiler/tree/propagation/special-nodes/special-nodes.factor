USING: accessors classes.algebra classes.tuple classes.tuple.private
combinators.short-circuit compiler.tree compiler.tree.propagation.info kernel
sequences slots.private words ;

IN: compiler.tree.propagation.special-nodes


! * Predicate hierarchy for class dispatch
PREDICATE: flushable-call < #call word>> flushable? ;
PREDICATE: slot-call < flushable-call word>> \ slot eq? ;
PREDICATE: literal-slot-call < slot-call
    in-d>> second value-info { [ literal?>> ] [ literal>> 0 = not ] } 1&& ; ! Exclude length slot calls

PREDICATE: rw-slot-call < literal-slot-call
    in-d>> first2 [ value-info class>> ] [ value-info literal>> ] bi* swap read-only-slot? not ;
PREDICATE: tuple-boa-call < flushable-call word>> \ <tuple-boa> eq? ;

PREDICATE: non-flushable-call < #call flushable-call? not ;
PREDICATE: inlined-call < non-flushable-call body>> >boolean ;
UNION: non-escaping-call flushable-call inlined-call ;

PREDICATE: set-slot-call < non-flushable-call word>> \ set-slot eq? ;
PREDICATE: literal-set-slot-call < set-slot-call in-d>> third value-info literal?>> ;
PREDICATE: tuple-set-slot-call < literal-set-slot-call in-d>> second value-info class>> tuple class<= ;

PREDICATE: tuple-push < #push literal>> tuple? ;
PREDICATE: mutable-tuple-push < tuple-push literal>> immutable-tuple-class? not ;
PREDICATE: sequence-push < #push literal>> fixed-length? ;
