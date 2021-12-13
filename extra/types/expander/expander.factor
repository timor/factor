USING: accessors assocs classes classes.algebra combinators continuations
effects generalizations kernel kernel.private macros.expander math memoize
namespaces quotations sequences words ;

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

! TODO: consider other domains for literalization, or should that be a type macro?
: state-literals ( state-in -- seq literal? )
    [ class of ] map dup [ wrapper? ] all?
    [ [ wrapped>> ] map t ]
    [ drop f f ] if ;

: macro-literals ( state-in n -- seq ? )
    over length over >=
    [ tail-slice* state-literals ]
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
    [ macro-effect macro-literals ] 2bi
    [ swap expand-static-macro ]
    [ drop expand-dynamic-macro ] if ;

: reset-expansions ( -- )
    \ type-expand-macro reset-memoized ;

: dropper ( literals -- quot )
    length [ drop ] n*quot ;

! This makes a non-trivial assumption:  If a word is foldable, it is *expected* to work correctly iff all inputs are literal.
: fold-expand ( state-in word -- code/f )
    [ stack-effect in>> length macro-literals ] keep swap
    [ [ drop dropper ] [ [ execute ] curry with-datastack [ literalize ] map >quotation ] 2bi compose ]
    [ 2drop f ] if ;

M: word type-expand*
    { { [ dup foldable? ] [ fold-expand ] }
      [ 2drop f ]
    } cond ;

M: \ nip type-expand* 2drop [ swap drop ] ;
M: \ ? type-expand* 2drop
    { [ { POSTPONE: f ?? ?? } declare nip nip ]
      [ { not{ POSTPONE: f } ?? ?? } declare drop nip ]
    } ;

M: \ call type-expand* drop
    1 macro-literals
    [ [ dropper ] [ first ] bi compose ]
    [ drop f ] if ;
