USING: accessors arrays ascii classes combinators combinators.short-circuit
effects io kernel make math math.parser namespaces sequences sequences.extras sets
strings ;

IN: types.unification

FROM: namespaces => set ;

! Syntactic first-order unification with row variables
! Note that types here are not factor classes, so some would call these kinds,
! probably

! TODO: handle terminated effects

MIXIN: type-expr
INSTANCE: sequence type-expr

! * Context variables
! Holds the current equation which is considered to not be part of the equation
! set while being tested
SYMBOL: current-equation
! Mapping type-vars to unique names
SYMBOL: name-bindings
SYMBOL: var-name-counters

! Set of equations in the problem
SYMBOL: equations
! TODO TBR? set of eliminated equations
SYMBOL: eliminated
SYMBOL: occurs-cache
! Try performing substitutions as we go in target equations
SYMBOL: targets


SYMBOL: debug
: when-debug ( quot level -- )
    debug get 0 or <= [ call ] [ drop ] if ; inline

: with-unification-context ( quot -- )
    '[
        H{ } clone name-bindings set
        H{ } clone var-name-counters set
        H{ } clone occurs-cache set
        targets off
        eliminated off
        equations off
        current-equation off
        _ call
    ] with-scope ; inline

! * Algorithmic Structures

! TUPLE: context
!     occurs                      ! cache occurrences
!     equations
!     eliminated                  ! we keep eliminated equalities here for later substitution
!     ;

! : <context> ( eqs -- obj )
!     H{ } clone swap f context boa ;

TUPLE: equation < identity-tuple
    { lhs type-expr read-only }
    { rhs type-expr read-only } ;
C: <equation> equation

! * Type expressions

! Unfortunately, variants don't support defining identity tuples
TUPLE: type-var < identity-tuple { name string read-only } ;
INSTANCE: type-var type-expr
C: <type-var> type-var

TUPLE: type-const < identity-tuple { obj read-only } ;
! NOTE: this would need to be some kind of type-equality relationship here,
! unless we replace the whole thing with inclusion constraints...
M: type-const equal?
    { [ drop type-const? ]
        [ [ obj>> ] bi@ = ] } 2&& ;

INSTANCE: type-const type-expr
C: <type-const> type-const

TUPLE: fun-type
    { consumption type-expr read-only }
    { production type-expr read-only } ;
INSTANCE: fun-type type-expr
C: <fun-type> fun-type

TUPLE: row-var < type-var ;
C: <row-var> row-var

! ∀-Quantified type scheme
! Regarding substitution, this will only substitute free variables in expr
! When encountered for unification, this will return expr with fresh variables for every bound-var in expr ;
TUPLE: type-scheme quantified-vars expr ;
C: <type-scheme> type-scheme
INSTANCE: type-scheme type-expr

! Either we use make to interpolate the row-var catch bindings, or we
! use an explicit expression for that, which sort of makes sense since it's
! defined as a different kind anyways...
! TODO Should maybe rename this to configuration or something
TUPLE: row-var-assignment
    { expressions read-only } ;
INSTANCE: row-var-assignment type-expr
C: <row-var=> row-var-assignment

PREDICATE: valid-row-var-assignment < row-var-assignment
    expressions>> rest-slice [ row-var? not ] all? ;

! ** Occurrence

! Check for free occurrence.  Quantified occurence is treated as black box
GENERIC: occurs?* ( var type-expr -- ? )
: occurs? ( var expr -- ? )
    occurs-cache get
    [ [ occurs?* ] 2cache ]
    [ occurs?* ] if* ;

M: sequence occurs?*
    [ occurs? ] with any? ;

M: row-var-assignment occurs?*
    expressions>> occurs? ;

M: type-var occurs?*
    eq? ;

M: type-const occurs?*
    2drop f ;

M: fun-type occurs?* ( var expr -- ? )
    { [ consumption>> occurs? ]
      [ production>> occurs? ]
    } 2|| ;

M: type-scheme occurs?*
    { [ quantified-vars>> in? not ]
      [ expr>> occurs? ]
    } 2&& ;

M: equation occurs?*
    { [ lhs>> occurs? ]
      [ rhs>> occurs? ] } 2|| ;

! Helper: modify a predicate so it skips a test for a specific value of elt,
! returns instead instead
:: skip= ( pred: ( obj -- ? ) elt instead -- pred: ( obj -- ? ) )
    [ dup elt = [ drop instead ] pred if ] ; inline

:: occurs-in-problem? ( var -- ? )
    { [ equations get
        [| e | var e occurs? ]
        current-equation get f skip= any? ]
      [ targets get
        [ var swap occurs? ] any?
      ]
    } 0|| ;

! ** Enumerating variables

GENERIC: vars ( type-expr -- seq )
M: sequence vars [ vars ] gather ;
M: type-var vars 1array ;
M: row-var vars 1array ;
M: type-const vars drop f ;
M: fun-type vars
    [ consumption>> vars ]
    [ production>> vars ] bi append members ;
M: equation vars
    [ rhs>> vars ] [ lhs>> vars ] bi append members ;
M: row-var-assignment vars
    expressions>> vars ;

! ** Substitution

! List of variables which are not to be substituted
GENERIC: subst-var ( new-expr old-var type-expr -- type-expr subst? )
M: type-var subst-var
    2dup = [ 2drop t ] [ 2nip f ] if ;
M: type-const subst-var
    2nip f ;
M: row-var subst-var
    2dup = [ 2drop t ] [ 2nip f ] if ;
M:: fun-type subst-var ( new old expr -- expr subst? )
    new old expr consumption>> subst-var :> ( con csub? )
    new old expr production>> subst-var :> ( prod psub? )
    csub? psub? or
    [ con prod <fun-type> t ]
    [ expr f ] if ;

! ! TODO: It may be necessary to establish this as separate constraint set
! : add-constraint ( new existing -- )
!     2dup <equation> 1array f swap update-context-with-equations
!     ;

! Substitute quantified variables, but establish constraints?
! For now, substitute quantified variables, causing next quantification to fail
M:: type-scheme subst-var ( new old expr -- expr' subst? )
    expr quantified-vars>> :> qvars
    old qvars in? drop f
    [ expr f ]
    [ new old expr expr>> subst-var
      [ qvars swap <type-scheme> t ]
      [ drop expr f ] if
    ] if ;

: expand-row-var-assignments ( seq -- seq )
    dup '[ _ [ dup row-var-assignment?
        [ expressions>> % ]
        [ , ] if
      ] each ] swap make ;

M: sequence subst-var
    [ subst-var 2array ] with with map
    unzip [ ] any?
    [ [ expand-row-var-assignments ] when ] keep
    ;

M: row-var-assignment subst-var
    [ expressions>> subst-var ] keep swap
    [ [ drop <row-var=> valid-row-var-assignment check-instance ]
      [ nip ] if  ] keep ;

M:: equation subst-var ( new old e -- equation subst? )
    new old e lhs>> subst-var :> ( lhs lhs-subst? )
    new old e rhs>> subst-var :> ( rhs rhs-subst? )
    lhs-subst? rhs-subst? or
    [ lhs rhs <equation> t ]
    [ e f ] if ;

: subst-var-in-equations ( new old equations -- equations )
    [ dup current-equation get =
      [ 2nip ]
      [ subst-var drop ] if
     ] 2with map ;

: subst-var-in-context ( var replacement -- )
    ! [ swap equations [ subst-var-in-equations ] change ] call
    [ swap equations [ subst-var-in-equations ] change ]
    ! [ swap eliminated [ subst-var-in-equations ] change ] 2bi
    [ swap targets [ subst-var-in-equations ] change ] 2bi
    ;
    ! [ equations>> subst-var-in-equations ]
    ! [ equations<< ] bi ;

! ** Conversion
GENERIC: element>type-expr ( element -- type-expr )
! TODO: actual types ( approach: create set of constraints already when converting? )
! Maps names to type-vars
SYMBOL: type-var-mappings
! FIXME: only used to separate reconstruction name space...
SYMBOL: row-var-mappings

: with-fresh-names ( quot -- )
    [ H{ } clone type-var-mappings ] dip with-variable ; inline

: with-fresh-mappings ( quot -- )
    H{ } clone row-var-mappings [ with-fresh-names ] with-variable ; inline

! ( ... var: type ... )
! NOTE: not supporting quantifier here yet, only types!  Those would need
! constraint support for dependent typing

SYMBOL: quantifier-stack

! This is used to stop collecting quantifier scope in effect output positions
SYMBOL: inhibit-collect-quantifiers
! If we are not currently inside a quantification scope, then we assume
! universal quantification
: quantified? ( type-var -- ? )
    quantifier-stack get
    [ drop t ] [ [ in? ] with any? ] if-empty ;

: inner-quantified? ( type-var -- ? )
    quantifier-stack get
    [ drop t ] [ last in? ] if-empty ;

: quantify-var ( type-var -- )
    inhibit-collect-quantifiers get
    [ drop ]
    [ dup quantified?
      ! dup inner-quantified?
      [ drop ] [ quantifier-stack get [ swap suffix ] change-last ] if ] if ;

: collecting-quantifiers ( quot -- seq )
    '[ quantifier-stack [ { } suffix ] change
       inhibit-collect-quantifiers off
       @
       quantifier-stack get last
    ] with-scope
    ; inline

: not-collecting-quantifiers ( quot -- )
    inhibit-collect-quantifiers swap with-variable-on ; inline

M: pair element>type-expr
    second element>type-expr ;

M: string element>type-expr
    type-var-mappings get [ <type-var> ] cache
    dup quantify-var ;

M: class element>type-expr
    <type-const> ;


! ** Conversion to Type Schemes
! DOING: reworking effect transformation into type schemes.  When parsing, all
! vars inside the body with the same name refer to the same type expression An
! effect will produce a type-scheme type-expr which has all vars quantified,
! EXCEPT the ones which already have been quantified in an outer scope.
! Whenever we parse the consumption of an effect, a new quantifier scope is
! opened.  This provides somthingh which I suspect is similar to let
! polyphormism...?
! Example: ( ..r1 -- ..r1 quot: ( ..a -- ..b ) quot: ( ..a -- ..b ) )
! 1. Outer scope, lhs:
!    1. quantify ..r1 in outer scope
! 2. Outer scope, rhs
!    1. Use quantified ..r1
!    2. First quotation Inner scope
!       1. lhs:
!          1. Quantify ..a in inner scope
!       2. rhs:
!          1. ..b free in inner scope
!    3. Second quotation Inner scope
!       1. lhs:
!          1. Quantify ..a in inner scope
!       2. rhs:
!          1. ..b free in inner scope


! Result:
! ∀r1.(..r1 → ..r1 ∀a.(a → b) ∀a.(a → b))

! Example: ( ..a1 b quot1: ( ..a1 -- ..c ) quot2: ( ..c b -- ..b2 ) -- ..b2 )
! - ..a1 and b outer scope lhs bindings
! - ..c free in quot1 scope, but part of lhs in outer scope
! - ..c in quot2 now quantified in outer scope already, b also
! - ..b2 free in quot2 scope, but quantified in outer scope
! - ..b2 then quantified correctly in outer scope when rhs is parsed


! Result:
! ∀a1,b,c,b2.(..a1 b ∀(..a1 → ..c) ∀(..c b → ..b2) → ..b2)

: consumption/production>type-expr ( row-var elements -- type-expr )
    [ element>type-expr ] map
    swap prefix ;

! non-provided row variables are always fresh
: ensure-row-var ( string/f -- row-var )
    row-var-mappings get [ <row-var> ] cache ;
    ! [ type-var-mappings get [ <row-var> ] cache ]
    ! [ "r" <row-var> ] if* ;

: effect-row-vars ( effect -- in-var out-var )
    [ in-var>> ] [ out-var>> ] bi
    2dup [ not ] both?
    [ 2drop "r" <row-var> dup ]
    [ [ ensure-row-var ] bi@ ]
    if ;
    ! Maybe quantify the input row var
    ! [ dup quantify-var ] dip ;

! Construct type expressions from effects
:: (effect>type-scheme) ( effect -- type-expr )
    effect [ effect-row-vars ]
    [ in>> ] [ out>> ] tri :> ( in-var out-var cons prod )
    [ in-var dup quantify-var
      cons [ element>type-expr ] map
      swap prefix
    ] collecting-quantifiers :> qvars
    ! [
        prod [ element>type-expr ] map
        out-var dup quantify-var
    ! ] not-collecting-quantifiers
    prefix <fun-type>
    qvars swap <type-scheme> ;
    ! [  ]
    ! swapd [ consumption/production>type-expr ] 2bi@
    ! <fun-type> ;

GENERIC: fresh-var-from ( type-var -- type-var )
M: type-var fresh-var-from
    name>> <type-var> ;
M: row-var fresh-var-from
    name>> <row-var> ;

! Instantiating a type scheme with fresh variables for unification
: instantiate-type-scheme ( type-scheme -- type-expr )
    [ expr>> ]
    [ quantified-vars>> ] bi
    [ [ fresh-var-from ] keep rot subst-var drop ] each ;

! ! This parses an effect with new name bindings.  This ensures that any names
! ! inside are unique.  This is used on the top level to add equations.
! : effect>type-expr ( effect -- type-expr )
!     ! (effect>type-expr) ;
!     [ (effect>type-expr) ] with-fresh-mappings ;

! : effect>type-scheme ( effect -- type-expr )
!     [ quantifier-stack [ { } clone suffix ]
!       (effect>type-expr)
!     ] with-scope ;

! NOTE: creates new name binding scope, use only top-level or quote-nested
: effect>type-expr ( effect -- type-expr )
    ! (effect>type-expr) ;
    [ (effect>type-scheme) ] with-fresh-mappings ;

M: effect element>type-expr
    (effect>type-scheme) ;
    ! (effect>type-expr) ;

! FIXME: used?
M: configuration element>type-expr
    elements>> [ element>type-expr ] map ;

! * Unification

ERROR: unification-conflict equation lhs rhs ;

! If var1 is not in term, and var1 occurs anywhere in the problem, substitute
! and remove
: eliminate-var? ( var rhs -- ? )
    { [ occurs? not ]
      [ drop occurs-in-problem? ]
    } 2&&
    drop f
    ;


! destructive
: eliminate-var ( var replacement -- )
    subst-var-in-context ;

PREDICATE: empty-sequence < sequence empty? ;

: unify-stacks ( seq1 seq2 -- new-eqs )
    2dup [ length 1 = ] [ length 1 = not ] bi* and
    [ swap ] when
    2dup [ length 1 = not ] [ length 1 = ] bi* and ! rest-decompose
    [ first swap <row-var=> valid-row-var-assignment check-instance
      2array 1array ]
    [ [ unclip-last-slice ] bi@
      swapd [ 2array ] 2bi@ 2array
    ] if ;

SINGLETON: keep-eqn

! Several cases:
! 1. var = exprn -> eliminate or keep
! 1. var1 = var2 -> if var2 does not occur in problem, keep
! 1. var1 = var2 -> if var2 does occur in problem -> swap

: swap? ( lhs rhs -- ? )
    {
        [ [ type-var? not ] [ type-var? ] bi* and ]
        [ { [ [ type-var? ] both? ]
            [ [ occurs-in-problem? not ] [ occurs-in-problem? ] bi* and ]
          } 2&& ]
    } 2|| ;


: unify-type-var ( var expr -- new-eqs )
    2dup eliminate-var?
    [ eliminate-var f ]
    [ 2drop keep-eqn ] if ;

DEFER: pp-type
! TODO: make sure that row-var = type-var throws an error?
! TODO: make sure that only row-vars can match stack sequences
: unify-type-exprs ( lhs rhs -- new-eqs )
    [
        "step:" print
        2dup [ pp-type nl ] bi@ nl
    ] 3 when-debug
    { { [ 2dup = ] [ 2drop f ] } ! delete (expensive)
      { [ 2dup [ sequence? ] both? ] [ unify-stacks ] } ! stack-decompose
      { [ 2dup swap? ] [ swap 2array 1array ] } ! swap
      { [ over type-var? ] [ unify-type-var ] }
      ! { [ 2dup [ empty-sequence? ] both? ] [ 2drop f ] } ! delete2, matching ! stacks completely decomposed (cheap?)
      ! { [ 2dup = ] [ 2drop f ] } ! delete3 (recursive)
      { [ 2dup [ type-scheme? ] both? ]
       [ [ instantiate-type-scheme ] bi@ 2array 1array ] } ! T-COMP
      { [ 2dup [ fun-type? ] both? ]
        [ [ [ consumption>> ] [ production>> ] bi ] bi@
          swapd [ 2array ] 2bi@ 2array ] }
      { [ 2dup [ row-var-assignment? ] both? ]
        [ [ expressions>> ] bi@ unify-stacks ] }
      [ current-equation get unification-conflict ]
    } cond ;

! Current strategy, probably too dumb:
! Until pass returns no changes, perform pass
! - take all equations from the set
! - for each equation, perform unification of lhs and rhs
!   - if anything changed, update set of equations, repeat
!   - if pass reports no changes, done

: maybe-keep-eliminated ( old-eq -- )
    dup lhs>> type-var?
    [ eliminated [ swap suffix ] change ] [ drop ] if ;

: remove-equation-from-context ( old-eq -- )
    [ equations [ remove-eq ] change ]
    [ maybe-keep-eliminated ] bi ;

ERROR: recursive-equation eqn ;

:: check-new-equation-for-recursion ( new-eq -- )
    new-eq lhs>> :> lhs
    lhs type-var?
    [
        lhs new-eq rhs>> occurs?
        [ new-eq recursive-equation ] when
    ] when ;

: check-for-recursion ( new-eqs -- new-eqs )
    dup [ check-new-equation-for-recursion ] each ;

: update-context-with-equations ( old-eq new-eqs -- )
    [ remove-equation-from-context ] dip
    check-for-recursion
    equations [ swap append ] with change ; ! NOTE: possibly prepending here could make a huge difference?

: unify-equation ( equation -- changed? )
    dup current-equation set
    dup [ lhs>> ] [ rhs>> ] bi
    unify-type-exprs dup keep-eqn?
    [ 2drop f ]
    [ [ <equation> ] { } assoc>map
      update-context-with-equations t
    ] if ;

DEFER: pprint-context
DEFER: pprint-unifier
: unify-context-pass ( -- changed? )
    [ pprint-context ] 2 when-debug
    equations get
    ! dup equations>>
    [ unify-equation ] any? ;

ERROR: safe-loop-count-exceeded ;

:: safe-loop ( ... pred: ( ... -- ... ? ) limit -- ... )
    0 \ safe-loop set-global
    [ \ safe-loop counter limit >= [ safe-loop-count-exceeded ] pred if ] loop ; inline

: unify-context ( equations -- )
    ! [
        equations set
        [ unify-context-pass
        ] 500 safe-loop
        [ pprint-unifier ] 1 when-debug
    ! ] with-fresh-mappings
    ! f >>occurs
    ;

! Calculate substitutions
: unify-configurations ( seq1 seq2 -- )
    <equation> 1array unify-context ;

: effects-unifier ( effect1 effect2 -- )
    [ effect>type-expr ] bi@
    [ production>> ] [ consumption>> ] bi* unify-configurations ;

! Context is fully unified iff:
! - lhs are distinct variables
! - no lhs occurs in any rhs (this cannot be checked if we allow recursive expressions?)

: var-in-rhs? ( var -- ? )
    equations get [ rhs>> occurs? ] with any? ;

ERROR: not-a-unifier equations ;

: check-unifier ( equations -- equations )
    dup [ lhs>> ] map
    {
        [ [ type-var? ] all? ]
        [ all-unique? ]
        ! [ [ var-in-rhs? ] any? not ]
    } 1&&
    [ not-a-unifier ] unless ;

! This is needed because if we want to substitute vars in the resulting fun
! type, binding-only equalities are not guaranteed to be on the lhs.
! Or there is a bug in the unifier.
: valid-reverse-equations ( equations -- equations )
    [ [ lhs>> ] [ rhs>> ] bi dup type-var?
      [ swap <equation> ]
      [ 2drop f ] if
    ] map sift ;

: context-unifier-equations ( -- equations )
    equations get
    eliminated get
    drop
    ! append
    ! check-unifier
    ! NOTE: Completely unsure whether this is legal!
    ! dup valid-reverse-equations append
    ;

! Apply all substitutions, in rest of substitutions and in targets
:: substitute-in-targets ( -- )
    equations get
    check-unifier :> eqns!
    [ eqns empty? ] [
        eqns unclip-slice :> ( rest next )
        next [ rhs>> ] [ lhs>> ] bi :> ( new old )
        rest [ new old rot subst-var drop ] map eqns!
        targets [ [ new old rot subst-var drop ] map ] change
    ] until ;


! ! NOTE: this presupposes that the context contains a valid unifier!
: substitute-with-context ( expr -- expr' )
    ! equations get check-unifier drop
    [ context-unifier-equations ] dip
    [ swap [ [ rhs>> ] [ lhs>> ] bi ] dip subst-var drop ] reduce ;

: substitute-configurations ( seq1 seq2 -- seq1' seq2' )
    [ substitute-with-context ] bi@ ;
    ! [ substitute-with-context ] bi* ;

GENERIC: simplify* ( type-expr -- type-expr' )
M: sequence simplify* [ simplify* ] map ;

SYMBOL: bound-row-vars
: bound-row-var? ( type-var -- ? )
    bound-row-vars get member? ;

M:: fun-type simplify* ( type-expr -- type-expr' )
    type-expr [ consumption>> ] [ production>> ] bi :> ( lhs rhs )
    lhs rhs [ unclip-slice ] bi@ :> ( lrest l1 rrest r1 )
    l1 r1 { [ [ bound-row-var? not ] both? ] [ = ] } 2&&
    [
        {
            [ l1 lrest occurs? ]
            [ r1 lrest occurs? ]
            [ l1 rrest occurs? ]
            [ r1 rrest occurs? ]
        } 0||
        [ f ] [ t ] if
    ] [ f ] if

    [ lrest simplify* rrest simplify* <fun-type> ]
    [ bound-row-vars [ l1 suffix r1 suffix ] change
      lhs simplify* rhs simplify* <fun-type>
    ] if ;

M: type-expr simplify* ;

: simplify ( type-expr -- type-expr' )
    { } bound-row-vars [ simplify* ] with-variable ;

DEFER: pp-type
: unify-effects-to-type ( effect1 effect2 -- fun-type )
    [ effect>type-expr ] bi@
    ! NOTE: expecting type schemes here
    [ expr>> ] bi@
    [
        "Unify expressions:" print
        2dup [ pp-type nl ] bi@
    ] 1 when-debug
    [ [ consumption>> ] [ production>> ] bi* 2array targets set ]
    [ [ production>> ] [ consumption>> ] bi* unify-configurations ] 2bi
    substitute-in-targets
    targets get first2
    ! substitute-configurations
    <fun-type>
    [ "Substituted: " write dup pp-type nl ] 1 when-debug
    simplify
    [ "Simplified: " write dup pp-type nl ] 1 when-debug
    ;
    ! [ [ consumption>> ] [ production>> ] bi* substitute-configurations
    !   <fun-type>
    !   ! simplify
    ! ]
    ! 2bi ;

! * Back Conversion
GENERIC: type-expr>element ( e -- elt )
: configuration>elements ( seq -- seq )
    [ type-expr>element ] map ;

! Unique var names: check if var is present (eq)
! If present, suffix has been calculated
! Check if

GENERIC: mappings-for-var ( type-var -- assoc )
M: type-var mappings-for-var drop type-var-mappings get ;
M: row-var mappings-for-var drop row-var-mappings get ;

GENERIC: counters-for-var ( type-var -- assoc )
M: type-var counters-for-var drop type-var-mappings get ;
M: row-var counters-for-var drop row-var-mappings get ;

: bound-var? ( type-var -- ? )
    name-bindings get key? ;

: register-bound-var ( type-var str -- )
    swap name-bindings get set-at ;

: var-basename ( name -- prefix )
    [ digit? ] trim-tail ;

:: inc-at* ( key assoc -- n )
    key assoc at
    ?1+ [ key assoc set-at ] keep ;

: next-suffix ( basename -- str )
    var-name-counters get inc-at* [ "" ] [ number>string ] if-zero ;

: new-var-name ( name -- name )
   var-basename dup next-suffix append ;

: bind-new-name ( type-var -- str )
    dup name>> new-var-name
    [ register-bound-var ] keep ;

: ensure-unique-name ( type-var -- string )
    name-bindings get ?at
    [ bind-new-name ] unless ;

M: type-var type-expr>element
    ensure-unique-name ;

! NOTE: analogous to forward conversion, the return name has no meaning!
M: type-const type-expr>element
    "x" swap obj>> 2array ;

ERROR: unexpected-row-var-in-configuration type-expr ;
M: row-var type-expr>element
    unexpected-row-var-in-configuration ;

! :: remove-ellipses ( fun-type -- cons-row prod-row consumption production )
!     fun-type [ consumption>> ] [ production>> ] bi
!     :> ( cons prod )
!     cons prod [ unclip-slice ] bi@ :> ( cons1 r1 prod2 r2 )
!     r1 r2 = [
!         {
!             ! FIXME: could be expensive without context cache
!             [ r1 cons1 occurs? ]
!             [ r2 cons1 occurs? ]
!             [ r1 prod2 occurs? ]
!             [ r2 prod2 occurs? ]
!             [ t ]
!         } 0||
!         [ r1 r2 cons1 prod2 ]
!         [ f f cons1 prod2 ] if
!     ] [ r1 r2 cons1 prod2 ] if ;

: extract-var-effect ( fun-type -- in-var out-var c-seq p-seq )
    [ consumption>> ] [ production>> ] bi
    2dup [ ?first row-var? ] both?
    [ [ unclip-slice ensure-unique-name swap ] bi@ swapd ]
    [ [ f f ] 2dip ] if
    ! [ [ dup [ ensure-unique-name ] when ] bi@ ] 2dip
    ;

M: type-scheme type-expr>element
    instantiate-type-scheme type-expr>element ;

M: fun-type type-expr>element
    extract-var-effect
    [ configuration>elements ] bi@
    swapd <variable-effect>
    "quot" swap 2array ;

: fun-type>effect ( fun-type -- effect )
    type-expr>element second ;

! Make sure that conversion and back do the same thing
ERROR: inconsistent-self-inference e1 e2 ;
: validate-scheme ( effect -- )
    dup effect>type-expr [ type-expr>element second ] with-unification-context
    2dup effect= [ 2drop ] [ inconsistent-self-inference ] if ;

! Probably makes sense to keep the constraints here
! once implemented using constraints
: unify-effects* ( effect1 effect2 -- effect3 )
    unify-effects-to-type fun-type>effect
    ! "Re-interpreted effect:" print
    ! dup effect>type-expr pp-type nl
    ;

: unify-effects ( effect1 effect2 -- effect3 )
    [ 2dup "Effects to unify: " print [ . ] bi@ ] 1 when-debug
    ! unify-effects* ;
    [ unify-effects* ] with-unification-context
    [ "Unified effect:" print dup . nl ] 1 when-debug
    ! dup validate-scheme
    ;

! * Prettyprint type expressions for debugging

GENERIC: pp-type* ( type-expr -- )
M: equation pp-type*
    [ lhs>> pp-type* "  =  " write ]
    [ rhs>> pp-type* ] bi ;

M: type-var pp-type*
    ensure-unique-name write ;

M: row-var pp-type*
    ensure-unique-name ".." prepend write ;

M: sequence pp-type*
    [ "∅" write ]
    [
        "{" write
        unclip-slice pp-type*
        [ " " write pp-type* ] each
        "}" write
    ] if-empty ;

M: row-var-assignment pp-type*
    "<" write expressions>> pp-type* ">" write ;

M: type-const pp-type*
    obj>> pprint ;

M: fun-type pp-type*
    "(" write
      [ consumption>> pp-type*
        " ⟶ " write
      ] [ production>> pp-type* ] bi
      ")" write ;

! TODO: probably wrong
M: type-scheme pp-type*
    "∀" write
    [ quantified-vars>> [ ensure-unique-name ] map "," join write ]
    [ ".(" write
        expr>> pp-type*
         ")" write ] bi ;

: pprint-context ( -- )
    nl "Context:" print
    ! [
        equations get
        [ pp-type* nl ] each
    ! ] with-fresh-mappings
    eliminated get [
        "Eliminated:" print
        [ pp-type* nl ] each
    ] when*
    targets get [
        "Targets:" print
        [ pp-type* nl ] each
    ] when*
    ;

: pprint-unifier ( -- )
    nl "Unifier:" print
    pprint-context
    "Substitutions:" print
    context-unifier-equations
    [ pp-type* nl ] each
    ;

: pp-type ( type-expr -- )
    pp-type* ;
    ! [ pp-type* ] with-fresh-mappings ;
