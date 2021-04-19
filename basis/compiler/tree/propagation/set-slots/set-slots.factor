USING: accessors classes.algebra combinators compiler.tree
compiler.tree.propagation.info compiler.tree.propagation.nodes kernel sequences
slots.private ;

IN: compiler.tree.propagation.set-slots

! * Set slot propagation

PREDICATE: set-slot-call < #call word>> \ set-slot eq? ;
PREDICATE: literal-set-slot-call < set-slot-call in-d>> third value-info literal?>> ;
PREDICATE: tuple-set-slot-call < literal-set-slot-call in-d>> second value-info class>> tuple class<= ;

! ! set-slot ( value obj n -- )
! : propagate-set-slot-call ( value-val obj-val n-val -- info )

M: tuple-set-slot-call propagate-before ( node -- )
    [ call-next-method ] keep
    propagate-rw-slots?
    [ {
            [ in-d>> first <1slot-ref> ]
            [ in-d>> third value-info literal>> 1 - ]
            [ in-d>> second value-info clone [ clone [ set-nth ] keep ] change-slots ]
            [ in-d>> second set-value-info ]
        } cleave
    ] [ drop ] if ;
