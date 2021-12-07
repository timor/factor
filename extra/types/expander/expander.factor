USING: accessors assocs combinators continuations kernel macros macros.expander
math quotations sequences types.protocols words ;

IN: types.expander

! * Type-value-state-dependent code expansion
! This expands into a quotation

! Can be used to read whether this contained run-time calls, e.g. the
! surrounding definition will have to be inlined.
SYMBOL: must-inline?

GENERIC: type-expand* ( state-in word -- code/f )
MEMO: type-expand ( state-in word -- code/f )
    type-expand* ;

: reset-expansions ( -- )
    \ type-expand reset-memoized ;

PREDICATE: recursive-primitive < word [ def>> ] [ 1quotation ] bi = ;
M: object type-expand* 2drop f ;

ERROR: undefined-primitive-expansion word ;
M: recursive-primitive type-expand*
    undefined-primitive-expansion ;

: macro-literals ( state-in macro -- seq ? )
    [ literal-value of ] [ macro-effect ] bi*
    2dup [ length ] dip >=
    [ tail* dup [ ] all? ]
    [ 2drop f f ] if ;

: expand-dynamic-macro ( macro-quot -- code )
    [ call call ] curry ;

ERROR: static-macro-expansion-error inputs macro-quot error ;
: expand-static-macro ( inputs macro-quot -- code )
    [ with-datastack last ]
    [ static-macro-expansion-error ]
    recover
    must-inline? on
    ;

: type-expand-macro ( state-in macro -- code )
    [ nip macro-quot ]
    [ macro-literals ] 2bi
    [ swap expand-static-macro ]
    [ drop expand-dynamic-macro ] if ;

M: word type-expand*
    { { [ dup macro? ] [ type-expand-macro ] }
      { [ dup inline? ] [ nip def>> ] }
      [ 2drop f ]
    } cond ;

M: \ declare type-expand*
