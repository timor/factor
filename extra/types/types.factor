USING: accessors arrays classes combinators combinators.short-circuit effects
generic kernel namespaces quotations sequences sets types.base-types
types.function-types types.syntax vocabs words ;

IN: types

FROM: namespaces => set ;

! * Predefined Type Schemes
! Retrieves typing judgments
GENERIC: type-of* ( word -- type )
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

M: generic type-of* ( word -- type )
    unknown-type-scheme ;

M: word type-of* ( word -- type )
    { { [ dup "input-classes" word-prop ] [ type-of-bootstrap-word ] }
      ! { [ dup "shuffle" word-prop ] [ type-of-shuffle-word ] }
      { [ dup "primitive" word-prop ] [ unknown-type-scheme ] }
      ! { [ dup "special" word-prop ] [ unknown-type-scheme ] }
      [ type-of-normal-word ]
    } cond ;

! constantly
: constantly ( x -- quot: ( -- x ) )
    [ ] curry ;
: unit ( x -- quot: ( -- x ) )
    1quotation ;
    ! ; ( ..a x -- ..a quot: ( ..b -- ..b x ) ) typed
: k ( ..a quot1 quot2: ( ..a -- ..b ) -- ..b )
    nip call ; inline

! * Minimal Combinator Base
! Complete bases
! 1. call, dip, curry, dup, drop, [ ]
! 2. curry, keep, k, [ ]
! 3. cake, k, [ ]
! 4. cake, if, [ ], f
! 5. curry, keep, fi, [ ], f

M: \ +any+ type-of* ;

: fi ( true false ? -- )
    rot if ; inline
M: \ fi type-of* drop
    "c" "A1" <maybe-type> "A2" 2array <all-type>
    { { "true" ( ..A1 -- ..B1 ) } { "false" ( ..A2 -- ..B2 ) } "c" }
    "c" "B1" <maybe-type> "B2" 2array <all-type>
    { } <variable-effect> ;

! For now, using conditional triplets and f :
! ( (A1[c!=f]|A2) c ( A1 → B1 ) ( A2 → B2 ) → (B1[c!=f]|B2) )

DEFER: infer-type
M: \ k type-of* drop
    [ f fi ] infer-type ;
    ! "a" "x" { "quot" ( ..a -- ..b ) } 2array
    ! "b" { } <variable-effect> ;
    ! { "A1" "A2" } <sum-type> { "dropped" ( ..A1 -- ..B1 ) } { "quot" ( ..A2 -- ..B2 ) } 2array
    ! "B2" { } <variable-effect> ;

    ! "a" "x" { "quot" ( ..a -- ..b ) } 2array
    ! "b" { } <variable-effect> ;
    ! "a" "d" <drop> { "quot" ( ..a -- ..b ) } 2array
    ! "b" { } <variable-effect> ;
    ! "a" "d" <dup-type> { "quot" ( ..a -- ..b ) } 2array
    ! "b" { } <variable-effect> ;
    ! "a" +drop+ { "quot" ( ..a -- ..b ) } 2array
    ! "b" { } <variable-effect> ;
    ! ( ..a x quot: ( ..a -- ..b ) -- ..b ) ;
    ! ( ..A dropped: ( ..A -- ..C ) quot: ( ..C -- ..B ) -- ..B ) ;
    ! ( ..A dropped: ( ..A -- ..C ) quot: ( ..A -- ..B ) -- ..B ) ;


! swap constantly swap compose
DEFER: cake
M: \ curry type-of* drop
    ( x quot: (  ..a x -- ..c ) -- quot: ( ..a -- ..c ) ) ;
    ! ( x quot: ( ..a y -- ..c ) -- quot: ( ..a -- ..c ) ) ;
    ! cake base:
    ! [ cake [ ] k ] infer-type ;
    ! [ cake drop ] infer-type ;

! ( ..r x quot: ( ..r x -- ..s ) -- ..s dup(x) )
! With Alternatives
! ( ..rho alt(b|b1) quot: ( ..rho b -- ..C ) -- ..C b1 )
M: \ keep type-of* drop
    "R" { "b" "b1" } <sum-type> ( ..R b -- ..C ) 2array
    "C" { "b1" } <variable-effect> ;
    ! "r" { "x" { "quot" ( ..r x -- ..s ) } }
    ! "s" "x" 1array <variable-effect>
    ! "r" { "x" { "quot" ( ..r x -- ..s ) } }
    ! "s" "x" <dup-type> 1array <variable-effect> ;
    ! "r"
    !  "x" "quot"
    !      "r" "x" <pred> 1array "s" { } <variable-effect>
    !      2array
    ! 2array
    ! "s" "x" <succ> 1array <variable-effect>
    ! ;

! ** Cake base

: take ( ..r b a -- ..r quot )
    [ dip ] curry curry ; inline
    ! swap '[ @ _ ] ;

: cake ( ..r b quotA: ( ..A b -- ..C ) -- ..r quot: ( ..A -- ..C ) quot: ( ..A -- ..C b ) )
    2dup take [ curry ] dip ;
    ! [ curry ]
    ! [ take ] 2bi ;

! M: \ cake type-of* drop
!     ! ( ..r b quotA: ( ..A b -- ..C ) -- ..r quot: ( ..A -- ..C ) quot: ( ..A -- ..C b ) ) ;
!     ! ( ..r b quotA: ( ..A -- ..C ) -- ..r quot: ( ..A -- ..C ) quot: ( ..A -- ..C b ) ) ;
!     ! ( ..r b quotA: ( ..A b -- ..C ) -- ..r quot: ( ..A -- ..C ) quot: ( ..A b -- ..C b ) ) ;
!     ( ..r b quotA: ( ..A x -- ..C ) -- ..r quot: ( ..A -- ..C ) quot: ( ..A -- ..C b ) ) ;
!     ! ( ..r b quotA: ( ..A x -- ..C ) -- ..r quot: ( ..A -- ..C ) quot: ( ..A b -- ..C b ) ) ;

! Effects for testing
: dupdupswap ( x -- x x2 x1 ) dup dup swap ;
! M: \ dupdupswap type-of* drop
!     "r" "a" 1array
!     "r" "a" "a" <dup-type> <dup-type> "a" <dup-type> 3array
!     <variable-effect> ;

! * Derived basic Combinators
M: \ dup type-of* drop
    [ [ ] keep ] infer-type ;
    ! [ [ ] cake dip dip ] infer-type ;

M: \ drop type-of* drop
    [ [ ] k ] infer-type ;

M: \ call type-of* drop
    [ dup k ] infer-type ;
    ! [ [ [ ] ] dip k ] infer-type ;

M: \ nip type-of* drop
    [ [ drop drop ] keep ] infer-type ;

M: \ dip type-of* drop
    [ [ nip call ] curry keep ] infer-type ;
    ! [ cake k ] infer-type ;

M: \ swap type-of* drop
    [ [ ] curry dip ] infer-type ;

M: \ over type-of* drop
    [ swap [ swap ] keep ] infer-type ;

M: \ 2dup type-of* drop
    [ over over ] infer-type ;

M: \ dupd type-of* drop
    [ [ dup ] dip ] infer-type ;

M: \ compose type-of* drop
    [ [ [ call ] dip call ] curry curry ] infer-type ;

M: \ pick type-of* drop
    [ [ dup ] 2dip [ swap ] dip swap ] infer-type ;

M: \ rot type-of* drop
    [ [ swap ] bi@ ] infer-type ;

M: \ -rot type-of* drop
    [ rot rot ] infer-type ;

M: \ if type-of* drop
    [ rot fi ] infer-type ;

: m ( -- ) dup call ; inline


! M: \ dup type-of* drop
!     { "x" } { "x" } "x" <dup-type> suffix <effect> ;

! That's an interesting one, because ..a needs to be fully inferred for this to
! be typed
M: \ loop type-of* drop
    ( ..a pred: ( ..a -- ..a ? ) -- ..a ) ;

! * Retrieving declared types for recursive cases
! For recursive words, we actually need to turn the declared effect into a type
! for the inner invocations
: recursive-call-type ( word -- type )
    ! "declared-effect" word-prop ;
    drop ( ..prev -- ..next ) ;

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
: type-of ( obj -- fun-type )
    type-of* effect>term
    ! assert-linear-type
    ! normalize-fun-type
    ;

M: quotation infer-type
    [ ( -- ) effect>term ]
    [ unclip-slice type-of
      ! [
          [ type-of unify-effects ] reduce
      ! ] with-unification-context
    ] if-empty ;

M: composed infer-type
    >quotation infer-type ;

M: curried infer-type
    >quotation infer-type ;

: quote-type ( type name -- effect )
    swap 2array 1array { } swap <effect> ;

M: curried type-of*
    >quotation type-of* ;

M: composed type-of*
    >quotation type-of* ;

! This is debatable, because typing it requires inference...
M: quotation type-of*
    infer-type "quot" quote-type ;

M: class type-of* "x" quote-type ;

M: object type-of* class-of "x" quote-type ;
