USING: accessors arrays assocs classes combinators combinators.short-circuit
effects kernel make math math.parser namespaces sequences sets strings ;

IN: types.unification

! Syntactic first-order unification with row variables
! Note that types here are not factor classes, so some would call these kinds,
! probably

! TODO: handle terminated effects

MIXIN: type-expr
INSTANCE: sequence type-expr

! * Algorithmic Structures

TUPLE: context
    occurs                      ! cache occurrences
    equations
    eliminated                  ! we keep eliminated equalities here for later substitution
    ;

: <context> ( eqs -- obj )
    H{ } clone swap f context boa ;

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

GENERIC: occurs?* ( context var type-expr -- ? )
:: occurs? ( context var expr -- ? )
    var expr context occurs>> [ [ context ] 2dip occurs?* ] 2cache ;

M: sequence occurs?*
    [ occurs? ] with with any? ;

M: row-var-assignment occurs?*
    expressions>> occurs?* ;

M: type-var occurs?*
    eq? nip ;

M: type-const occurs?*
    3drop f ;

M:: fun-type occurs?* ( context var expr -- ? )
    { [ context var expr consumption>> occurs? ]
      [ context var expr production>> occurs? ]
    } 0|| ;

M: equation occurs?* ( context var equation -- ? )
    { [ lhs>> occurs? ]
      [ rhs>> occurs? ] } 3|| ;

! Helper: modify a predicate so it skips a test for a specific value of elt,
! returns instead instead
:: skip= ( pred: ( obj -- ? ) elt instead -- pred: ( obj -- ? ) )
    [ dup elt = [ drop instead ] pred if ] ; inline

:: occurs-in-problem? ( context eqn var -- ? )
    context equations>>
    [| e | context var e occurs? ]
    eqn f skip= any? ;

! ** Enumerating variables

! possibly unused?
GENERIC: vars ( type-expr -- seq )
M: sequence vars [ vars ] gather ;
M: type-var vars 1array ;
M: row-var vars 1array ;
M: fun-type vars
    [ consumption>> vars ]
    [ production>> vars ] bi append members ;

! ** Substitution
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
    [ subst-var drop ] 2with map ;

! destructive
: subst-var-in-context ( var replacement context -- )
    swapd
    [ equations>> subst-var-in-equations ]
    [ equations<< ] bi ;

! ** Conversion
GENERIC: element>type-expr ( element -- type-expr )
! TODO: actual types ( approach: create set of constraints already when converting? )
SYMBOL: mappings
! FIXME: only used to separate reconstruction name space...
SYMBOL: row-var-mappings

: with-fresh-names ( quot -- )
    [ H{ } clone mappings ] dip with-variable ; inline

: with-fresh-mappings ( quot -- )
    H{ } clone row-var-mappings [ with-fresh-names ] with-variable ; inline

! ( ... var: type ... )
! NOTE: not supporting quantifier here yet, only types!  Those would need
! constraint support for dependent typing
M: pair element>type-expr
    second element>type-expr ;

M: string element>type-expr
    mappings get [ <type-var> ] cache ;

M: class element>type-expr
    <type-const> ;

: consumption/production>type-expr ( row-var elements -- type-expr )
    [ element>type-expr ] map
    swap prefix ;

! non-provided row variables are always fresh
: ensure-row-var ( string/f -- row-var )
    [ mappings get [ <row-var> ] cache ]
    [ "." <row-var> ] if* ;

! If neither effect is specified, use ".", but quantified for both sides
: effect-row-vars ( effect -- in-var out-var )
    [ in-var>> ] [ out-var>> ] bi
    2dup [ not ] both?
    [ 2drop "." <row-var> dup ]
    [ [ ensure-row-var ] bi@ ]
    if ;

! Construct type expressions from effects
: (effect>type-expr) ( effect -- type-expr )
    [ effect-row-vars ]
    [ in>> ] [ out>> ] tri
    swapd [ consumption/production>type-expr ] 2bi@
    <fun-type> ;

: effect>type-expr ( effect -- type-expr )
    [ (effect>type-expr) ] with-fresh-mappings ;

M: effect element>type-expr
    (effect>type-expr) ;

M: configuration element>type-expr
    elements>> [ element>type-expr ] map ;

! * Unification

ERROR: unification-conflict context equation lhs rhs ;

: eliminate-var? ( context eqn var rhs -- ? )
    { [ nipd occurs? not ]
      [ drop occurs-in-problem? ]
    } 4 n&& ;

! If var1 is not in term, and var1 occurs anywhere in the problem, substitute
! and remove

! destructive
: eliminate-var ( context var replacement -- )
    rot subst-var-in-context ;

PREDICATE: empty-sequence < sequence empty? ;

: unify-stacks ( seq1 seq2 -- new-eqs )
    2dup [ length 1 = ] [ length 1 = not ] bi* and
    [ swap ] when
    2dup [ length 1 = not ] [ length 1 = ] bi* and ! rest-decompose
    [ first swap <row-var=> valid-row-var-assignment check-instance 2array 1array ]
    [ [ unclip-last-slice ] bi@
      swapd [ 2array ] 2bi@ 2array
    ] if ;

SINGLETON: keep-eqn

: unify-type-var ( context eqn var expr -- new-eqs )
    {
        ! { [ dup type-var? ] [ 4drop keep-eqn ] }
      { [ 4dup eliminate-var? ] [ nipd eliminate-var f ] } ! eliminate
      [ 4drop keep-eqn ]
    } cond ;

! TODO: make sure that row-var = type-var throws an error?
! TODO: make sure that only row-vars can match stack sequences
: unify-type-exprs ( context eqn lhs rhs -- new-eqs )
    { { [ 2dup eq? ] [ 4drop f ] } ! delete1 (cheap)
      { [ over type-var? ] [ unify-type-var ] }
      { [ dup type-var? ] [ swap 2array 1array 2nip ] } ! swap
      { [ 2dup [ empty-sequence? ] both? ] [ 4drop f ] } ! delete2, matching ! stacks completely decomposed (cheap?)
      { [ 2dup [ sequence? ] both? ] [ 2nipd unify-stacks ] } ! stack-decompose
      { [ 2dup = ] [ 4drop f ] } ! delete3 (recursive)
      { [ 2dup [ fun-type? ] both? ]
        [ [ [ consumption>> ] [ production>> ] bi ] bi@
          swapd [ 2array ] 2bi@ 2array 2nip ] }
      { [ 2dup [ row-var-assignment? ] both? ]
        [ 2nipd [ expressions>> ] bi@ unify-stacks ] }
      [ unification-conflict ]
    } cond ;

! Current strategy, probably too dumb:
! Until pass returns no changes, perform pass
! - take all equations from the set
! - for each equation, perform unification of lhs and rhs
!   - if anything changed, update set of equations, repeat
!   - if pass reports no changes, done

: maybe-keep-eliminated ( context old-eq -- context )
    dup lhs>> type-var?
    [ swap [ swap suffix ] change-eliminated ] [ drop ] if ;

: remove-equation-from-context ( context old-eq -- context )
    [ swap [ remove-eq ] with change-equations ]
    [ maybe-keep-eliminated ] bi
    ;

: update-context-with-equations ( context old-eq new-eqs -- context )
    [ remove-equation-from-context ] dip
    '[ _ append ] change-equations ; ! NOTE: possibly prepending here could make a huge difference?


! :: update-context-with-equations ( context old-eq new-eqs -- context )
!     context [
!         old-eq swap remove-eq
!         new-eqs append !
!     ] change-equations ;

: unify-equation ( context equation -- context changed? )
    ! break
    2dup dup [ lhs>> ] [ rhs>> ] bi
    unify-type-exprs dup keep-eqn?
    [ 2drop f ]
    [ [ <equation> ] { } assoc>map
      update-context-with-equations t
    ] if ;

: unify-context-pass ( context -- context changed? )
    dup equations>>
    [ unify-equation ] any? ;

: unify-context ( context -- context )
    [ unify-context-pass ] loop
    ! f >>occurs
    ;

! Calculate substitutions
: unify-configurations ( seq1 seq2 -- context )
    <equation> 1array <context> unify-context ;

: effects-unifier ( effect1 effect2 -- context )
    [ effect>type-expr ] bi@
    [ production>> ] [ consumption>> ] bi* unify-configurations ;

! Context is fully unified iff:
! - lhs are distinct variables
! - no lhs occurs in any rhs (this cannot be checked if we allow recursive expressions?)

: var-in-rhs? ( context var -- ? )
    over equations>> [ rhs>> ] map
    [ occurs? ] 2with any? ;

ERROR: not-a-unifier context ;

: check-context-unification ( context -- context )
    dup equations>> [ lhs>> ] map
    {
        [ [ type-var? ] all? ]
        [ all-unique? ]
        [ dupd [ var-in-rhs? ] with any? not ]
    } 1&&
    [ not-a-unifier ] unless ;

! This is needed because if we want to substitute vars in the resulting fun
! type, binding-only equalities are not guaranteed to be on the lhs.
! Or there is a bug in the unifier.
! : add-reverse-substitutions ( context -- context )
!     dup equations>>
!     [ [ lhs>> ] [ rhs>> ] bi
!       dup type-var?
!       [ swap <equation> ]
!       [ 2drop f ] if
!     ] map sift
!     '[ _ append ] change-equations ;

: valid-reverse-equations ( equations -- equations )
    [ [ lhs>> ] [ rhs>> ] bi dup type-var?
      [ swap <equation> ]
      [ 2drop f ] if
    ] map sift ;

: context-unifier-equations ( context -- equations )
    [ equations>> ]
    [ eliminated>> ] bi
    append
    dup valid-reverse-equations append
    ;


! ! NOTE: this presupposes that the context contains a valid unifier!
: substitute-with-context ( context expr -- expr' )
    [ check-context-unification ] dip
    [ context-unifier-equations ] dip
    [ swap [ [ rhs>> ] [ lhs>> ] bi ] dip subst-var drop ] reduce ;

: substitute-configurations ( context seq1 seq2 -- seq1' seq2' )
    [ [ substitute-with-context ] keepd ]
    [ substitute-with-context ] bi* ;

: unify-effects-to-type ( effect1 effect2 -- fun-type )
    [ effect>type-expr ] bi@
    [ [ production>> ] [ consumption>> ] bi* unify-configurations ]
    [ [ consumption>> ] [ production>> ] bi* substitute-configurations
      <fun-type> ]
    2bi ;

! * Back Conversion
GENERIC: type-expr>element ( e -- elt )
: configuration>elements ( seq -- seq )
    [ type-expr>element ] map ;

! Unique var names: check if var is present (eq)
! If present, suffix has been calculated
! Check if

GENERIC: mappings-for-var ( type-var -- assoc )
M: type-var mappings-for-var drop mappings get ;
M: row-var mappings-for-var drop row-var-mappings get ;

: suffix-for-new-var ( type-var -- string )
    [ name>> ] [ mappings-for-var ] bi
    [ [ -1 or 1 + ] change-at ]
    [ at ] 2bi
    [ "" ] [ number>string ] if-zero ;

: unique-name-suffix ( type-var -- string )
    mappings get ?at
    [
        [ suffix-for-new-var ] keep
        [ mappings get set-at ] keepd
    ] unless ;

: ensure-unique-name ( type-var -- string )
    dup name>> "." =
    [ name>> ]
    [ [ name>> ] keep unique-name-suffix append ] if ;

M: type-var type-expr>element
    ensure-unique-name ;

! NOTE: analogous to forward conversion, the return name has no meaning!
M: type-const type-expr>element
    "x" swap obj>> 2array ;

ERROR: unexpected-row-var-in-configuration type-expr ;
M: row-var type-expr>element
    unexpected-row-var-in-configuration ;

: shave-off-var-effect ( fun-type -- in-var out-var c-seq p-seq )
    [ consumption>> ] [ production>> ] bi
    [ unclip-slice ensure-unique-name swap ] bi@ swapd ;

! TODO: Possibly cut out variable effect here for replicating existing behavior
M: fun-type type-expr>element
    shave-off-var-effect
    [ configuration>elements ] bi@
    swapd <variable-effect>
    "quot" swap 2array ;

: fun-type>effect ( fun-type -- effect )
    [ type-expr>element ] with-fresh-mappings ;

! Probably makes sense to keep the constraints here
! once implemented using constraints
: unify-effects ( effect1 effect2 -- effect3 )
    unify-effects-to-type fun-type>effect second ;
