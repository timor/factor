USING: accessors arrays classes.algebra combinators compiler.tree
compiler.tree.propagation.info compiler.tree.propagation.nodes kernel math
sequences slots.private vectors ;

IN: compiler.tree.propagation.set-slots

! * Set slot propagation

PREDICATE: set-slot-call < #call word>> \ set-slot eq? ;
PREDICATE: literal-set-slot-call < set-slot-call in-d>> third value-info literal?>> ;
PREDICATE: tuple-set-slot-call < literal-set-slot-call in-d>> second value-info class>> tuple class<= ;

! ! set-slot ( value obj n -- )
! : propagate-set-slot-call ( value-val obj-val n-val -- info )

: ensure-slot-vector ( n seq/f -- n seq )
    >vector over 1 + f pad-tail ; inline

! TODO: maybe delegate info creation/manipulation to info.factor?
M: tuple-set-slot-call propagate-before ( node -- )
    [ call-next-method ] keep
    propagate-rw-slots?
    ! f
    [ {
            ! [ in-d>> first <1slot-ref> ]
            [ in-d>> first value-info ]
            [ in-d>> third value-info literal>> 1 - ]
            [ in-d>> second value-info clone [ V{ } or clone
                                               ensure-slot-vector
                                               [ set-nth ] keep ] change-slots ]
            [ in-d>> second set-value-info ]
        } cleave
    ] [ drop ] if ;
