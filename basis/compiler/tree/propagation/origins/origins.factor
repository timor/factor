USING: accessors combinators.short-circuit compiler.tree
compiler.tree.propagation.escaping compiler.tree.propagation.info
compiler.tree.propagation.nodes compiler.tree.propagation.special-nodes kernel
sequences sets ;
IN: compiler.tree.propagation.origins

! * Tracking object origins

SINGLETON: literal-allocation
SINGLETON: local-allocation

TUPLE: input-ref { index read-only } ;
: <input-ref> ( index -- obj )
    input-ref boa [ record-allocation ] keep ;


M: #introduce propagate-origin
    out-d>> [ <input-ref> 1register-origin ] each-index ;

! TODO: move input-escapes to propagate-after so annotation of input infos stays correct
: values-escape ( seq -- )
    propagate-rw-slots? [ [ container-escapes ] each ] [ drop ] if ;

: in-escapes ( node -- )
    in-d>> values-escape ;

: out-escapes ( node -- )
    out-d>> [ limbo 1register-origin ] each ;

GENERIC: call-in-escapes ( #call -- )
M: #call call-in-escapes
    in-escapes ;
M: non-escaping-call call-in-escapes drop ;
M: literal-set-slot-call call-in-escapes drop ;
M: non-literal-sequence-set-slot-call call-in-escapes drop ;

M: #call propagate-origin
    out-escapes ;

! TODO: This is currently a definition.  This should be inferred if IPO origin
! tracking is used.
! NOTE: Until IPO origin tracking is used, considering this only safe for the
! container object.
M: local-allocating-call propagate-origin
    out-d>> [ local-allocation 1register-origin ] each ;

M: inlined-call propagate-origin drop ;
M: set-slot-call propagate-origin drop ;

! Read-only slots inherit container origin
M: ro-slot-call propagate-origin
    [ in-d>> first value-info origin>> ]
    [ out-d>> first swap register-origin ] bi ;

! All other slots only inherit literal origin, if origin is not known beforehand
M: slot-call propagate-origin
    dup out-d>> first value-info origin>>
    [ drop ]
    [ dup in-d>> first value-info origin>> HS{ literal-allocation } set=
      [ out-d>> first literal-allocation 1register-origin ]
      [ out-d>> first invalidate-object ] if
    ] if ;

M: #alien-node propagate-origin
    out-escapes ;

M: #push propagate-origin
    out-d>> [ literal-allocation 1register-origin ] each ;

: value-info-escapes? ( info -- ? )
    {
        [ origin>> limbo swap in? ]
        [ slots>> [ dup [ value-info-escapes? ] when ] any? ]
        [ summary-slot>> dup [ value-info-escapes? ] when ]
    } 1||
    ;
