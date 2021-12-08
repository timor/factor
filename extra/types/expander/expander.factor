USING: accessors assocs combinators continuations generalizations kernel
kernel.private macros macros.expander math memoize namespaces quotations
sequences types.protocols words ;

IN: types.expander

! * Type-value-state-dependent code expansion
! This expands into a quotation

! Can be used to read whether this contained run-time calls, e.g. the
! surrounding definition will have to be inlined.
SYMBOL: must-inline?

GENERIC: type-expand* ( state-in word -- code/f )
: type-expand ( state-in word -- code/f )
    type-expand* ;

M: object type-expand* 2drop f ;

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

MEMO: type-expand-macro ( state-in macro -- code )
    [ nip macro-quot ]
    [ macro-literals ] 2bi
    [ swap expand-static-macro ]
    [ drop expand-dynamic-macro ] if ;

: reset-expansions ( -- )
    \ type-expand-macro reset-memoized ;

M: word type-expand* 2drop f ;
M: \ nip type-expand* 2drop [ swap drop ] ;
M: \ ? type-expand* 2drop
    { [ { POSTPONE: f ?? object } declare nip nip ]
      [ { not{ POSTPONE: f } object ?? } declare drop nip ]
    } ;
