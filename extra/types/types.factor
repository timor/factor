USING: accessors arrays classes combinators combinators.short-circuit effects
generic kernel namespaces quotations sequences sets types.syntax
types.unification words ;

IN: types

FROM: namespaces => set ;


! * Predefined Type Schemes
! Retrieves typing judgments
GENERIC: type-of ( word -- type )
ERROR: unknown-type-scheme word ;

DEFER: infer-word-type
: cache-infer-type ( word -- type )
    dup infer-word-type
    [ "inferred-type-scheme" set-word-prop ] keep ;

: reset-type-caches ( -- )
    all-words [ "inferred-type-scheme" remove-word-prop ] each ;

: type-of-normal-word ( word -- type )
    { [ "declared-type-scheme" word-prop ]
      ! [ "inferred-type-scheme" word-prop ]
      ! [ cache-infer-type ]
      [ infer-word-type ]
      ! [ unknown-type-scheme ]
    } 1|| ;

: classes>elements ( seq -- seq )
    [ "x" swap 2array ] map ;

: type-of-bootstrap-word ( word -- type )
    [ "input-classes" word-prop ]
    [ "default-output-classes" word-prop ] bi
    [ classes>elements ] bi@
    <effect> ;

: type-of-shuffle-word ( word -- type )
    "shuffle" word-prop ;

M: generic type-of ( word -- type )
    unknown-type-scheme ;

M: word type-of ( word -- type )
    { { [ dup "input-classes" word-prop ] [ type-of-bootstrap-word ] }
      { [ dup "shuffle" word-prop ] [ type-of-shuffle-word ] }
      { [ dup "primitive" word-prop ] [ unknown-type-scheme ] }
      ! { [ dup "special" word-prop ] [ unknown-type-scheme ] }
      [ type-of-normal-word ]
    } cond ;

! constantly
: constantly ( x -- quot: ( -- x ) )
    [ ] curry
    ; ( ..a x -- ..a quot: ( ..b -- ..b x ) ) typed
: quote ( x -- quot: ( -- x ) )
    1quotation
    ; ( ..a x -- ..a quot: ( ..b -- ..b x ) ) typed

! M: \ swap type-of drop
!     ( a b -- b a ) ;
M: \ compose type-of drop
    ( ... quot1: ( ..a -- ..b ) quot2: ( ..b -- ..c ) -- ... quot: ( ..a -- ..c ) ) ;
M: \ call type-of drop
    ( ..a quot: ( ..a -- ..b ) -- ..b ) ;
M: \ dip type-of drop
    ( ..a b quot: ( ..a -- ..c ) -- ..c b ) ;
M: \ if type-of drop
    ( ..a ?: boolean true: ( ..a -- ..b ) false: ( ..a -- ..b ) -- ..b ) ;
! TODO: curry

! That's an interesting one, because ..a needs to be fully inferred for this to
! be typed
M: \ loop type-of drop
    ( ..a pred: ( ..a -- ..a ? ) -- ..a ) ;

! * Retrieving declared types for recursive cases
! For recursive words, we actually need to turn the declared effect into a type
! for the inner invocations
: recursive-call-type ( word -- type )
    "declared-effect" word-prop ;

! * Quotation type inference
! TODO: clean up terminology.  Currently types and effects are used a bit inconsistently
GENERIC: infer-type ( obj -- effect )

! TODO: catch recursion, which needs to depend on predefined stack effects
! TODO: make sure that type caching cannot become inconsistent when only parts
! of inner words change with regards to recursive inferences?
SYMBOL: inference-trace

: with-inference-trace ( quot -- )
    [ HS{ } clone inference-trace ] dip with-variable ; inline

:: check-recursion ( quot: ( ..a word -- ..b ) rec: ( ..a word -- ..b ) -- quot2: ( ..a word -- ..b ) )
    [ dup inference-trace get in?
      rec
      [ [ inference-trace get adjoin ] quot bi ] if ]
    ; inline

: infer-word-type ( word -- type )
    [ infer-type ] [ recursive-call-type ] check-recursion with-inference-trace ;

M: word infer-type
    def>> infer-type ;

M: generic infer-type
    unknown-type-scheme ;

FROM: types.bn-unification => unify-effects ;
M: quotation infer-type
    [ ( -- ) ]
    [ unclip-slice type-of
      ! [
          [ type-of unify-effects ] reduce
      ! ] with-unification-context
    ] if-empty ;

: quote-type ( type name -- effect )
    swap 2array 1array { } swap <effect> ;

! This is debatable, because typing it requires inference...
M: quotation type-of
    infer-type "quot" quote-type ;

M: object type-of class-of "x" quote-type ;
