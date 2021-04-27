USING: accessors combinators.short-circuit compiler.tree
compiler.tree.propagation.copy compiler.tree.propagation.info
compiler.tree.propagation.nodes compiler.tree.propagation.special-nodes kernel
sequences sets ;
IN: compiler.tree.propagation.origins

! * Tracking object origins

M: #introduce propagate-origin
    out-d>> [ <input-ref> 1register-origin ] each-index ;

! TODO: move input-escapes to propagate-after so annotation of input infos stays correct
: in-escapes ( node -- )
    propagate-rw-slots?
    [ in-d>> [ object-escapes ] each  ] [ drop ] if ;

: out-escapes ( node -- )
    out-d>> [ limbo 1register-origin ] each ;

GENERIC: call-in-escapes ( #call -- )
M: #call call-in-escapes
    in-escapes ;
M: non-escaping-call call-in-escapes drop ;
M: set-slot-call call-in-escapes drop ;

M: #call propagate-origin
    out-escapes ;

! TODO: This is currently a definition.  This should be inferred if IPO origin
! tracking is used.
M: local-allocating-call propagate-origin
    out-d>> [ local-allocation 1register-origin ] each ;

M: inlined-call propagate-origin drop ;
M: set-slot-call propagate-origin drop ;

M: #alien-node propagate-origin
    out-escapes ;

M: #push propagate-origin
    [ out-d>> first ] [ literal>> ] bi <literal-allocation> 1register-origin ;

: value-info-escapes? ( info -- ? )
    {
        [ origin>> limbo swap in? ]
        [ slots>> [ dup [ value-info-escapes? ] when ] any? ]
    } 1||
    ;
