USING: accessors arrays combinators.short-circuit effects kernel quotations
sequences types.syntax types.unification words ;

IN: types

FROM: namespaces => set ;

! * Predefined Type Schemes
! Retrieves typing judgements
GENERIC: type-of ( word -- type )
ERROR: unknown-type-scheme word ;

: type-of-normal-word ( word -- type )
    { [ "declared-type-scheme" word-prop ]
      [ "declared-effect" word-prop ]
      [ unknown-type-scheme ]
    } 1|| ;

: classes>elements ( seq -- seq )
    [ "x" swap 2array ] map ;

M: word type-of
    dup "input-classes" word-prop
    [ [ [ "default-output-classes" word-prop ] ] dip
      [ classes>elements ] bi@ <effect>
    ] [ type-of-normal-word ] if* ;

! ! constantly
! : constantly ( x -- quot: ( -- x ) )
!     [ ] curry
!     ; ( ..a x -- ..a quot: ( ..b -- ..b x ) ) typed

! M: \ swap type-of drop
!     ( a b -- b a ) ;
M: \ compose type-of drop
    ( quot1: ( ..a -- ..b ) quot2: ( ..b -- ..c ) -- quot: ( ..a -- ..c ) ) ;
M: \ call type-of drop
    ( ..a quot: ( ..a -- ..b ) -- ..b ) ;
M: \ dip type-of drop
    ( ..a b quot: ( ..a -- ..c ) -- ..c b ) ;
M: \ if type-of drop
    ( ..a ?: boolean true: ( ..a -- ..b ) false: ( ..a -- ..b ) -- ..b ) ;

! That's an interesting one, because ..a needs to be fully inferred for this to
! be typed
M: \ loop type-of drop
    ( ..a pred: ( ..a -- ..a ?: boolean ) -- ..a ) ;

! * Quotation type inference
! TODO: clean up terminology.  Currently types and effects are used a bit inconsistently
GENERIC: infer-type ( obj -- effect )
M: word infer-type
    def>> infer-type ;
M: quotation infer-type
    [ ( -- ) ]
    [ unclip-slice type-of
      [ type-of unify-effects ] reduce
    ] if-empty ;

: quote-type ( type name -- effect )
    swap 2array 1array { } swap <effect> ;

! This is debatable, because typing it requires inference...
M: quotation type-of
    infer-type "quot" quote-type ;

M: object type-of class-of "x" quote-type ;
