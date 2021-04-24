USING: accessors compiler.tree compiler.tree.propagation.info
compiler.tree.propagation.copy
compiler.tree.propagation.nodes compiler.tree.propagation.reflinks kernel
sequences math ;
IN: compiler.tree.propagation.origins

! * Tracking object origins

M: #introduce propagate-origin
    out-d>> [ <input-ref> 1register-origin ] each-index ;

! TODO: move input-escapes to propagate-after so annotation of input infos stays correct
: in-escapes ( node -- )
    in-d>> [ object-escapes ] each ;

: out-escapes ( node -- )
    out-d>> [ limbo 1register-origin ] each ;

GENERIC: call-in-escapes ( #call -- )
M: #call call-in-escapes
    in-escapes ;
M: non-escaping-call call-in-escapes drop ;
M: set-slot-call call-in-escapes drop ;

M: #call propagate-origin
    out-escapes ;
    ! [ in-escapes ] [ out-escapes ] bi ;


M: flushable-call propagate-origin
    [ out-d>> ] [ word>> ] bi '[ dup _ <call-result> 1register-origin ] each ;

M: inlined-call propagate-origin drop ;
M: set-slot-call propagate-origin drop ;

: register-slot-ref ( #call -- )
    [ out-d>> first ]
    [ in-d>> first2 [ resolve-copy ] [ value-info literal>> ] bi* <tuple-slot-ref> ] bi
    1register-origin ;

! slot ( obj m -- value )
M: literal-slot-call propagate-origin
    register-slot-ref ;
    ! [ out-d>> first ]
    ! [ in-d>> first2 [ value-info ] bi@
    !   [ slots>> ]
    !   [ literal>> 1 - ] bi* swap ?nth
    !   [ origin>> ] [ HS{ limbo } clone ] if*
    ! ] bi register-origin ;

! M: tuple-boa-call propagate-origin
!     out-d>> first dup <local-allocation> 1register-origin ;

M: #alien-node propagate-origin
    [ in-escapes ] [ out-escapes ] bi ;

M: #push propagate-origin
    [ out-d>> first ] [ literal>> ] bi <literal-allocation> 1register-origin ;
