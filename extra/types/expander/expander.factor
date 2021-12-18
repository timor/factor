USING: accessors arrays assocs classes classes.algebra classes.algebra.private
classes.builtin combinators combinators.smart continuations effects
generalizations inverse kernel kernel.private macros.expander math memoize
namespaces quotations sequences sets words ;

IN: types.expander

! * Type-value-state-dependent code expansion
! This expands into a quotation

! Can be used to read whether this contained run-time calls, e.g. the
! surrounding definition will have to be inlined.
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
    ! must-inline? on
    ;

! MEMO: type-expand-macro ( state-in macro -- code )
: type-expand-macro ( state-in macro -- code )
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

ERROR: invalid-literal-call-argument thing ;
GENERIC: type>quotations ( classoid -- quots )
M: wrapper type>quotations
    wrapped>> dup callable? [ 1array ] [ drop f ] if ;
M: anonymous-union type>quotations
    members>> [ type>quotations ] gather
    dup [ ] all? [ drop f ] unless ;
M: classoid type>quotations drop f 1array ;

M: \ call type-expand* drop
    ?last
    [
        class of type>quotations sift
        [ f ] [ [ [ drop ] prepose ] map dup length 1 = [ first ] when ] if-empty
    ]
    [ f ] if* ;

: run-type-macro ( stack quot -- quot/f )
    2dup [ length ] [ inputs ] bi* >=
    [ with-datastack last ]
    [ 2drop f ] if ;

! : declare-dropper ( effect-elements -- quot )
!     [ dup pair? [ second ] [ drop ?? ] if ] map
!     [ [ declare ] curry ] [ length [ drop ] n*quot ] bi compose ;
: (expand-commutative) ( a b -- quot/f )
    {
        { [ [ <wrapper> ] bi@ ]
          [ [  ] 2curry [ 2drop ] prepose ] }
        { [ <wrapper> swap ] [ nip 1quotation [ swap drop ] prepose ] }
        { [  ] [ 2drop f ] }
    } switch ;

: expand-commutative ( stack word -- quot/f )
    [ [ (expand-commutative) ] with-datastack last ] dip swap
    [ 1quotation compose ]
    [ drop f ] if* ;

: (expand-tag) ( type-value -- quot/f )
    class of builtins get
    [ class= ] with find
    nip [ "type" word-prop '[ drop _ ] ]
    [ num-types get ] if* ;

M: \ tag type-expand* drop
    [ (expand-tag) ] run-type-macro ;

: definitely-same-value? ( value1 value2 -- ? )
    [ value-id of ] bi@ = ;
    ! { [ [ cardinality 1 = ] both? ]
    !   [ [ members first ??? ] either? not ]
    !   [ [ members first ] same? ]
    ! } 2&& ;

: definitely-different-value? ( value1 value2 -- ? )
    type-values-intersect? not ;

M: \ eq? type-expand* drop
    [ { { [ 2dup definitely-same-value? ] [ 2drop [ 2drop t ] ] }
        { [ 2dup definitely-different-value? ] [ 2drop [ 2drop f ] ] }
        [ 2drop f ]
      } cond
    ] run-type-macro ;
