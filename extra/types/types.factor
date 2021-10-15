USING: accessors arrays assocs classes classes.tuple combinators
combinators.short-circuit effects generic io kernel kernel.private lists
macros.expander math namespaces prettyprint quotations sequences
sequences.private sets types.base-types types.function-types types.util
types.value-types vocabs words ;

IN: types

FROM: namespaces => set ;

! * Predefined Type Schemes
! Retrieves typing judgments
GENERIC: type-of* ( word -- type )
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
      [
          infer-word-type
          ! [ infer-word-type ]
          ! [ drop stack-effect ] recover
      ]
      ! [ unknown-type-scheme ]
    } 1|| ;

: classes>elements ( seq -- seq )
    [ "x" swap 2array ] map ;

: type-of-bootstrap-word ( word -- type )
    [ "input-classes" word-prop ]
    [ { [ "default-output-classes" word-prop ] [ "declared-effect" word-prop out>> ] } 1|| ] bi
    [ classes>elements ] bi@
    <effect> ;

: type-of-shuffle-word ( word -- type )
    "shuffle" word-prop ;

! M: generic type-of* ( word -- type )
!     unknown-type-scheme ;
ERROR: cannot-instantiate-var-args word ;

ERROR: unknown-type-scheme word ;

: configuration>ports ( seq -- list )
    [ dup pair? [ first ] when ] map sequence>list ;

! : defer-word ( word in out -- in out )
!     [ <primitive-type> ] 2keep
!     swapd [ suffix ] dip ;

: deferred-computation ( word -- lazy-computation )
    dup stack-effect in>> <lazy-computation> ;

: deferred-results ( computation word -- seq )
    stack-effect out>> length
    [ swap <eval-result> ] with { } map-integers ;

: configuration>values ( values types -- seq )
    swap [ <value-type> ] 2map ;

: blackbox-inputs ( word -- in )
    stack-effect in>> ;
    ! [ in>> ] [ effect-in-types ] bi configuration>values ;

: blackbox-output-values ( values word -- seq )
    drop ;
    ! stack-effect effect-out-types configuration>values ;

: blackbox-outputs ( word -- out )
    [ deferred-computation ]
    [ deferred-results  ]
    [ blackbox-output-values ] tri ;

: infer-blackbox ( word -- type )
    [ blackbox-inputs "A" swap ]
    [ blackbox-outputs "A" swap ] bi
    <variable-effect> ;

    ! word stack-effect :> e
    ! e variable-effect? [ cannot-instantiate-var-args ] when
    ! e [ in>> ] [ out>> ] bi :> ( in out )
    ! e [ effect-in-types ] [ effect-out-types ] bi :> ( in-types out-types )
    ! "A" in-types in [ <value-type> ] 2map
    ! "A" word in <lazy-computation> 1array
    ! <variable-effect> ;

    ! dup stack-effect dup [ in>> ]
    ! [ stack-effect dup variable-effect? [ cannot-instantiate-var-args ] when
    !   finite-effect>configurations
    ! ] keep <blackbox-type> ;
    ! dup stack-effect
    ! [ stack-effect dup ]
    ! [ stack-effect
    !   dup variable-effect? [ cannot-instantiate-var-args ] when
    !   [ in>> ] [ out>> ] bi
    !   [ "A" sequence>list* ] bi@ ] keep
    ! <primitive-type> ;
    ! [ configuration>ports ] bi@
    ! defer-word
    ! [ "A" tuck ] dip <primitive-type> ;


DEFER: infer-type*
: macro-call-type ( word -- type )
    [ macro-quot ] [ macro-effect ] bi [ call call ] swap [ [ curry ] prepose ] times curry
    infer-type* ;
!      [ macro-quot '[ _ ] ] [ macro-effect ] bi


M: word type-of* ( word -- type )
    {
        ! { [ dup "input-classes" word-prop ] [ type-of-bootstrap-word ] }
        ! { [ dup "shuffle" word-prop ] [ type-of-shuffle-word ] }
        { [ dup generic? ] [ infer-blackbox ] }
        { [ dup "primitive" word-prop ] [ unknown-type-scheme ] }
        { [ dup macro-quot ] [ macro-call-type ] }
        [ type-of-normal-word ]
    } cond ;

M: \ context-object type-of*
    infer-blackbox ;

M: predicate type-of*
    infer-blackbox ;
    ! drop
    ! "A" { +any+ }
    ! "A" { { "x" boolean } } <variable-effect> ;

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

M: \ fi type-of* drop
    ! "c" "A1" <maybe-type> "A2" 2array <all-type>
    "c" "A1" "A2" <choice-type>
    ! "A1" "A2" 2array <all-type>
    ! { "A1" "A2" } <sum-type>
    { { "true" ( ..A1 -- ..B1 ) } { "false" ( ..A2 -- ..B2 ) } "c" }
    "c" "B1" "B2" <choice-type>
    ! "c" "B1" <maybe-type> "B2" 2array <all-type>
    { } <variable-effect> ;

! For now, using conditional triplets and f :
! ( (A1[c!=f]|A2) c ( A1 → B1 ) ( A2 → B2 ) → (B1[c!=f]|B2) )

M: \ k type-of* drop
    [ f fi ] infer-type* ;
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
    ! [ cake [ ] k ] infer-type* ;
    ! [ cake drop ] infer-type* ;

! ( ..r x quot: ( ..r x -- ..s ) -- ..s dup(x) )
! With Alternatives
! ( ..rho alt(b|b1) quot: ( ..rho b -- ..C ) -- ..C b1 )
M: \ keep type-of* drop
    "R" { "b" "b1" } <sum-type> ( ..R b -- ..C ) 2array
    "C" { "b1" } <variable-effect> ;

    ! "R" "b"
    ! "R" { "b" "b1" } <sum-type> 1array "C" { } <variable-effect>
    ! ! ( ..R b -- ..C )
    ! 2array
    ! "C" { "b1" } <variable-effect> ;


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
    [ [ ] keep ] infer-type* ;
    ! [ [ ] cake dip dip ] infer-type* ;

M: \ drop type-of* drop
    [ [ ] k ] infer-type* ;

M: \ call type-of* drop
    [ dup k ] infer-type* ;
    ! [ [ [ ] ] dip k ] infer-type* ;

M: \ nip type-of* drop
    [ [ drop drop ] keep ] infer-type* ;

M: \ dip type-of* drop
    [ [ nip call ] curry keep ] infer-type* ;
    ! [ cake k ] infer-type* ;

M: \ swap type-of* drop
    [ [ ] curry dip ] infer-type* ;

M: \ over type-of* drop
    [ swap [ swap ] keep ] infer-type* ;

M: \ 2dup type-of* drop
    [ over over ] infer-type* ;

M: \ 2drop type-of* drop
    [ drop drop ] infer-type* ;

M: \ 3drop type-of* drop
    [ drop drop drop ] infer-type* ;

M: \ dupd type-of* drop
    [ [ dup ] dip ] infer-type* ;

M: \ swapd type-of* drop
    [ [ swap ] dip ] infer-type* ;

M: \ compose type-of* drop
    [ [ [ call ] dip call ] curry curry ] infer-type* ;

M: \ pick type-of* drop
    [ [ dup ] 2dip [ swap ] dip swap ] infer-type* ;

M: \ rot type-of* drop
    [ [ swap ] bi@ ] infer-type* ;

M: \ if type-of* drop
    [ rot fi ] infer-type* ;

M: \ -rot type-of* drop
    [ rot rot ] infer-type* ;

M: \ 3dup type-of* drop
    [ pick pick pick ] infer-type* ;

M: \ 2nip type-of* drop
    [ nip nip ] infer-type* ;

: m ( -- ) dup call ; inline

! M: \ dup type-of* drop
!     { "x" } { "x" } "x" <dup-type> suffix <effect> ;

! That's an interesting one, because ..a needs to be fully inferred for this to
! be typed
! M: \ loop type-of* drop
!     ( ..a pred: ( ..a -- ..a ? ) -- ..a ) ;

! * Retrieving declared types for recursive cases
! For recursive words, we actually need to turn the declared effect into a type
! for the inner invocations
: recursive-call-type ( word -- type )
    {
        [ "declared-type-scheme" word-prop ]
        ! [ "declared-effect" word-prop ]
        [ drop ( ..prev -- ..next ) ]
    } 1|| ;

! * Quotation type inference
! TODO: clean up terminology.  Currently types and effects are used a bit inconsistently
GENERIC: infer-type* ( obj -- effect )

! TODO: catch recursion, which needs to depend on predefined stack effects
! TODO: make sure that type caching cannot become inconsistent when only parts
! of inner words change with regards to recursive inferences?
SYMBOL: inference-trace

: with-inference-trace ( quot -- )
    [ { } clone inference-trace ] dip with-variable ; inline

:: check-recursion ( quot: ( ..a word -- ..b ) rec: ( ..a word -- ..b ) -- quot2: ( ..a word -- ..b ) )
    dup inference-trace get in?
    rec
    [ [ [ inference-trace [ swap suffix ] change ] quot bi ] with-scope ] if
    ; inline

SYMBOL: inferred-word-types

: infer-type ( callable -- type )
    H{ } clone inferred-word-types [ infer-type* ] with-variable ;

: infer-word-type ( word -- type )
    inferred-word-types get
    [ [ [ infer-type* ] [ recursive-call-type ] check-recursion ] cache ]
    [ [ infer-type* ] [ recursive-call-type ] check-recursion ] if*
    ;

M: word infer-type*
    def>> infer-type* ;

M: generic infer-type*
    unknown-type-scheme ;

FROM: types.bn-unification => unify-effects ;
: (type-of) ( obj -- fun-type )
    ! [ type-of* ] [ recursive-call-type ] check-recursion
    type-of*
    effect>term
    ! assert-linear-type
    ! normalize-fun-type
    ;

: type-of ( obj -- fun-type )
    ! [ (type-of) [ recursive-call-type ] check-recursion ]  with-inference-trace ;
    [ H{ } clone inferred-word-types set (type-of) ]
    with-inference-trace ;

SYMBOL: history

M: quotation infer-type*
    [ ( -- ) effect>term ]
    [ unclip-slice (type-of)
      V{ } clone history [
          [ [
                  [ "Infer word: " write dup . ] 1 when-debug
                  (type-of) unify-effects ]
            [ history get push ] bi
          ] reduce
      ] with-variable
    ] if-empty ;

M: composed infer-type*
    >quotation infer-type* ;

M: curried infer-type*
    >quotation infer-type* ;

: quote-type ( type name -- effect )
    swap 2array 1array { } swap <effect> ;

M: curried type-of*
    >quotation type-of* ;

M: composed type-of*
    >quotation type-of* ;

M: quotation type-of*
    infer-type* "quot" quote-type ;

PREDICATE: tuple-constructor < word "constructor-class" word-prop ;
M: tuple-constructor type-of*
    "constructor-class" word-prop
    dup all-slots [ dup class>> dup object = [ drop name>> ] [ nip ] if ] map
    <tuple-type> "x" quote-type ;

! * Interfacing with the Type system

GENERIC: literal>type ( object -- type )
M: object literal>type class-of ;
M: fixnum literal>type <type-const> ;
M: sequence literal>type
    length literal>type "e" <sequence-type> ;
M: tuple literal>type
    [ class-of ] [ tuple-slots [ literal>type ] map ] bi
    <tuple-type> ;
! M: f literal>type drop <f-type> "f" quote-type ;
! M: f literal>type drop "f" ;
M: f literal>type drop <f-type> ;
M: class literal>type <type-const> ;

! M: object type-of* literal>type "x" quote-type ;
! M: class type-of* literal>type "class" quote-type ;
! TODO: use annotated type-var instead
M: object type-of*
    <literal-value> "x" quote-type ;
    ! drop
    ! ( ..a -- ..a x ) ;
    ! [ class-of ] keep <value-type> "x" quote-type ;
M: f type-of* drop <f-type> "x" quote-type ;

! * Predefining some Generics types
! M: \ + type-of* drop
!     number "x" <value-type> number "y" <value-type> 2array
!     number \ + { "x" "y" } <lazy-computation> <value-type> 1array
!     <effect> ;

! M: \ length type-of* drop
!     "s" "l" "e" <sequence-type> 2array 1array
!     "l" 1array <effect> ;
! M: \ <= type-of* drop
!     [ - neg? ] infer-type* ;

M: \ = type-of*
    infer-blackbox ;

! * Monadic foo
M: \ set-at type-of* drop
    ( k v accum: ( k v -- ) -- ) ;
    ! [ 2curry ] infer-type* ;
    ! "k" "v" ( ..a -- ..b k v ) 3array
    ! { } <effect> ;
    ! "k" "v" [ 2array ] [ set-assoc-type ] 2bi suffix
    ! { } <effect> ;

! M: \ < type-of* drop
!     [ [ <= ] [ = not ] 2bi and ] infer-type* ;


! ( s: sequence -- l: integer ) ;

! Is boa a combinator? Or rather, a dependent type???
! : boa ( ..a class -- ..b ( ..a class -- ..b tuple:{ class slots }) )
! : boa ( (..foo-and-a-slot|..foo) tuple-class(n,m) -- ..(foo-and-slots[n!=m]|..foo  )
! : boa ( ..a (class|class1) -- ..a boa(class,n) )
! PREDICATE: empty-array < array { } = ;
! M: \ suffix type-of* drop
!     [ swap curry ] infer-type* ;
! M: \ prefix type-of* drop
!     [ swap take ] infer-type* ;
! M: array type-of*
!     >quotation
!     [ array prefix ] curry infer-type* ;
! M: \ new type-of* drop
!     [ [ ] swap prefix ] infer-type* ;
