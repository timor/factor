USING: accessors combinators combinators.short-circuit compiler.tree
compiler.tree.propagation.escaping compiler.tree.propagation.info
compiler.tree.propagation.copy
compiler.tree.propagation.nodes compiler.tree.propagation.special-nodes kernel math
sequences sets sets.extras ;

IN: compiler.tree.propagation.slot-refs

! slot ( obj m -- value )
: propagate-rw-slot-infos ( #call -- )
    [ in-d>> second value-info literal>> ]
    [ in-d>> first value-info
      [ 1 - ] [ slots>> ] bi* ?nth
    ]
    [ out-d>> first
      over [ set-value-info ] [ 2drop ] if
    ] tri
    ;

M: literal-slot-call propagate-before
    [ call-next-method ] keep
    propagate-rw-slots? [
        propagate-rw-slot-infos ] [ drop ] if ;
