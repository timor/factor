USING: accessors arrays assocs assocs.extras classes classes.tuple
colors.constants combinators combinators.short-circuit continuations
disjoint-sets disjoint-sets.private graphs hashtables hashtables.identity
io.styles kernel lexer make match math math.order math.parser namespaces parser
prettyprint.backend prettyprint.config prettyprint.custom prettyprint.sections
quotations sequences sets strings types.util unicode vectors words words.symbol
;

IN: terms

FROM: syntax => _ ;
FROM: namespaces => set ;

! * Specialized to not cause loops
TUPLE: eq-disjoint-set < tuple
    { parents identity-hashtable read-only }
    { ranks identity-hashtable read-only }
    { counts identity-hashtable read-only } ;

: <eq-disjoint-set> ( -- obj )
    IH{ } clone IH{ } clone IH{ } clone eq-disjoint-set boa ;

SYMBOL: no-defined-equalities
M: eq-disjoint-set equiv?
    representatives eq? ;
M:: eq-disjoint-set representative ( a disjoint-set -- p )
    a disjoint-set parents>> at :> p
    a p eq? [ a ] [
        p disjoint-set representative [
            a disjoint-set set-parent
        ] keep
    ] if ;

M: eq-disjoint-set disjoint-set-member? parents>> key? ;

M: eq-disjoint-set disjoint-set-members parents>> keys ;

M: eq-disjoint-set equiv-set-size
    [ representative ] keep counts>> at ;

M: eq-disjoint-set add-atom (add-atom) ;

M:: eq-disjoint-set equate ( a b disjoint-set -- )
    a b disjoint-set representatives
    2dup eq? [ 2drop ] [
        2dup disjoint-set ranks
        [ swap ] [ over disjoint-set inc-rank ] [ ] branch
        disjoint-set link-sets
    ] if ;

M: eq-disjoint-set clone
    [ parents>> ] [ ranks>> ] [ counts>> ] tri [ clone ] tri@ eq-disjoint-set boa ;

! * State
TUPLE: var-context { eqs eq-disjoint-set read-only } { ground-values assoc read-only } ;
M: var-context clone call-next-method
    [ eqs>> clone ] [ ground-values>> clone ] bi var-context boa ;


SYMBOL: defined-equalities-ds

! Using local for debugging
: defined-equalities ( -- ds )
    defined-equalities-ds get-global [ eqs>> ] [ f ] if* ; inline

: defined-ground-values ( -- assoc )
    defined-equalities-ds get-global ground-values>> ; inline

<PRIVATE
SYMBOL: globals-stack
PRIVATE>

:: with-global-variable ( value var quot -- )
    ! var get-global "Save: %u\n" printf
    [
        globals-stack [ var get-global suffix ] change
        value var set-global
        quot
        [
            globals-stack get last var set-global
            globals-stack [ but-last-slice ] change
            ! dup "Restore: %u\n" printf
            ! var set-global
        ] finally
    ] with-scope
    ; inline

! TODO: this is expensive!
SYMBOL: check-vars?
ERROR: unknown-term-vars v1 v2 ;
: check-vars ( v1 v2 ds -- )
    2over rot [ disjoint-set-member? ] curry both?
    [ 2drop ] [ unknown-term-vars ] if ; inline

: safe-equiv? ( v1 v2 ds -- ? )
    3dup check-vars
    equiv? ; inline

: defined-equal? ( v1 v2 -- ? )
    defined-equalities
    [
        ! check-vars? get [ 2over check-vars ] when
        ! safe-equiv? ] [ 2drop f ] if*
        equiv? ] [ 2drop f ] if*
    ; inline

: check-integrity ( -- )
    defined-equalities parents>> [ nip ] assoc-all?
    [ defined-equalities "Bad" 2array throw ] unless ;

: with-var-context ( var-context quot -- )
    defined-equalities-ds swap '[
        @
        check-integrity
    ] with-global-variable ; inline

! Using local scope for now, replace with global when working!
: with-eq-scope ( disjoint-set quot -- )
    [ H{ } clone var-context boa ] dip
    with-var-context
    ; inline

DEFER: vars
: with-term-vars ( obj quot -- )
    ! 2dup swap . .
    [ vars <eq-disjoint-set> [ add-atoms ] keep ] dip
    with-eq-scope ; inline

! : import-vars ( seq -- )
!     defined-equalities add-atoms ;

DEFER: term-vars
: import-term-vars ( term -- )
    f defined-equalities-ds [ term-vars ] with-global-variable
    defined-equalities
    [ 2dup disjoint-set-member? [ 2drop ] [ add-atom ] if ] curry each ;

! * Unique naming

MIXIN: id-name
: name-ize ( str -- str )
    dup [ digit? ] all? [ "_" append ] when ; inline
: string>id-name ( str -- name-part id-part/f )
    name-ize [ digit? not ] cut-when* [ f ] when-empty ; foldable
! PREDICATE: varname-string < string string>id-name  ;
INSTANCE: string id-name
GENERIC: name-part ( id-name -- str )
GENERIC: id-part ( id-name -- id/f )
GENERIC#: <id-name> 1 ( id-name id -- id-name )
M: string name-part string>id-name drop ; inline
M: string id-part string>id-name nip string>number ; inline
M: string <id-name> [ name-part ] dip number>string append ;

SYMBOL: var-names
var-names [ H{ } clone ] initialize

: reset-var-names ( -- )
    H{ } clone var-names set-global ;

: with-var-names ( quot -- )
    [ H{ } clone var-names ] dip
    with-variable ; inline

: get-name-suffix ( key -- name )
    dup name-part var-names get at <id-name> ;

: update-var-suffix ( key -- )
    [ id-part 0 or ]
    [ name-part var-names get ] bi
    [ 0 or max 1 + ] change-at ; inline

: uvar ( key -- name )
    [ update-var-suffix ]
    [ get-name-suffix ] bi ;

: uvar-shuffle ( in out -- in out )
    [ [ uvar ] map ] dip
    [ get-name-suffix ] map ;

! Named gensym
: usym ( name -- word )
    uvar <uninterned-word> ;

! : umatchvar ( name -- word )
!     usym dup
!     t "match-var" set-word-prop ;

DEFER: <term-var>
: utermvar ( name -- word )
    uvar <term-var> ;
    ! t "term-var" set-word-prop ;

! * Term variables
PREDICATE: term-var < word "term-var" word-prop ;

! FIXME: inlining this method causes mass recompile
M: term-var equal?
    over term-var?
    [ defined-equal? ] [ 2drop f ] if ;

! inline

: define-term-var ( name -- )
    create-word-in [ define-symbol ]
    [ t "term-var" set-word-prop ]
    bi ;

M: term-var pprint*
    name>> H{ { foreground COLOR: solarized-blue } } styled-text ;

M: term-var reset-word
    [ call-next-method ]
    [ f "term-var" set-word-prop ] bi ;

SYNTAX: TERM-VARS: ";" [ define-term-var ] each-token ;

: <term-var> ( name -- var )
    <uninterned-word>
    dup t "term-var" set-word-prop
    defined-equalities
    [ dupd add-atom ] when* ;

GENERIC: child-elts* ( obj -- nodes )
M: object child-elts* drop f ;
M: sequence child-elts* ;
M: string child-elts* drop f ;
M: tuple child-elts* tuple-slots ;

GENERIC: vars* ( obj -- )
M: object vars* drop ;
M: match-var vars* , ;
M: term-var vars* , ;
M: wrapper vars* wrapped>> vars* ;
! M: sequence vars* [ vars* ] each ;
! M: tuple vars* tuple-slots vars* ;

: vars ( obj -- seq )
    [ [ [ vars* ] [ child-elts* ] bi ] closure drop ] { } make ; inline

: term-vars ( obj -- seq )
    vars [ term-var? ] filter ;

: match-vars ( obj -- seq )
    vars [ match-var? ] filter ;

! * Ground Values

SYMBOL: ground-values

! : maybe-add-atom ( x ds -- )
!     2dup disjoint-set-member?
!     [ 2drop ] [ add-atom ] if ; inline

ERROR: ground-value-contradiction old value ;
ERROR: recursive-ground-terms terms ;

: check-recursive-terms ( assoc -- )
    [ term-vars member-eq? ] assoc-filter
    dup assoc-empty? [ drop ] [ recursive-ground-terms ] if ;
! FIXME: definition order!
DEFER: lift
: update-ground-values! ( assoc -- )
    [ [ keys ] keep [ [ f lift ] change-at ] curry each ]
    [ check-recursive-terms ] bi
    ; inline

:: define-ground-value ( var value ds -- )
    var ds
    representative defined-ground-values
    [
        [| old | old [ old value = [ old ] [ old value ground-value-contradiction ] if ]
         [ value ] if
        ] change-at
    ] [ update-ground-values! ] bi
    ; inline

: ground-value? ( obj -- ? )
    vars empty? ; inline

! Keep track of ground terms for equivalence classes
: ?ground-value ( var -- val/key )
    dup term-var?
    [ defined-equalities
      [
          representative
          defined-ground-values ?at drop
      ] when*
    ] when ;
    ! [ defined-equalities
    !   [ representative
    !     defined-ground-values ?at drop ] when* ] when ;
     ! ;

: maybe-update-ground-values ( a b -- )
    2drop defined-ground-values update-ground-values! ;
    ! [ defined-ground-values ] 2dip pick [ key? ] curry either?
    ! [ update-ground-values ground-values set ] [ drop ] if ;

! Main entry point for atoms
:: assume-equal ( a b -- )
    defined-equalities :> ds
    { { [ a b [ term-var? ] both? ] [ a b [ ds equate ] [ maybe-update-ground-values ] 2bi ] }
      { [ a term-var? ] [ a b ds define-ground-value  ] }
      { [ b term-var? ] [ b a ds define-ground-value  ] }
      [ a b "trying to make something other than term vars equal" 3array throw ]
    } cond ;

! * Unification
! Baader/Nipkow
GENERIC: subst ( assoc term -- assoc term )
SINGLETON: __

! This is for matching ground-terms only, basically as if expecting something that can be wrapped
TUPLE: atom-match var ;
C: <atom-match> atom-match


SYMBOL: in-quotation?
SYMBOL: current-subst

M: object subst ;
M: term-var subst
    over ?at drop
    ?ground-value
    dup { [ drop in-quotation? get ] [ word? ] [ { [ deferred? ] [ match-var? not ] } 1|| ] } 1&& [ <wrapper> ] when
    ;
M: match-var subst
    over ?at drop ;
M: sequence subst
    dup quotation?
    in-quotation? [ [ subst ] map ] with-variable ;
! As an exception, we don't rebuils vectors!
M: vector subst
    dup quotation?
    in-quotation? [ [ subst ] map! ] with-variable ;
! M: array subst
!     dup quotation?
!     in-quotation? [ [ subst ] map! ] with-variable ;
M: callable subst
    in-quotation? [ call-next-method ] with-variable-on ;
M: tuple subst tuple>array subst >tuple ;
M: wrapper subst wrapped>>
    in-quotation? [ subst ] with-variable-off
    <wrapper> ;
M: atom-match subst
    var>> subst dup ground-value? [ <atom-match> ] unless ;

: lift ( term subst -- term )
    swap subst nip ;

GENERIC: occurs? ( var term -- ? )
M: object occurs? 2drop f ;
M: match-var occurs? = ;
M: term-var occurs? eq? ;
M: sequence occurs? [ occurs? ] with any? ;
M: tuple occurs? tuple-slots occurs? ;

ERROR: rebuilds-identity-tuple term ;
M: identity-tuple subst rebuilds-identity-tuple ;

ERROR: incompatible-terms term1 term2 ;

SYNTAX: A{ scan-object "}" expect <atom-match> suffix! ;
M: atom-match pprint* pprint-object ;
M: atom-match pprint-delims drop \ A{ \ } ;
M: atom-match >pprint-sequence var>> 1array ;

! Tried first
GENERIC#: decompose-left 1 ( term1 term2 -- terms1 terms2 cont? )
GENERIC: decompose-right ( term1 term2 -- terms1 terms2 cont? )
M: object decompose-right f ;
M: object decompose-left decompose-right ;
M: tuple decompose-right
    2dup [ class-of ] same?
    [ [ tuple-slots ] bi@ t ] [ f ] if ;
M: sequence decompose-right
    2dup { [ [ class-of ] same? ] [ [ length ] same? ] } 2&& ;


: decompose ( term1 term2 -- term1 term2 cont? )
    {
        [
            { [ decompose-left ] [ decompose-right ] } 0||
            [ 2dup = [ f ] [ incompatible-terms ] if ] unless*
        ]
    } cond ;

SYMBOL: valid-match-vars
: valid-term-var? ( var -- ? )
    dup { [ term-var? ] [ match-var? ] } 1|| [
        valid-match-vars get
        [ in? ] [ drop t ] if*
    ] [ drop f ] if ; inline

DEFER: elim
DEFER: (solve)
! NOTE:
! - rhs term-vars will always be assumed to the lhs value
! - lhs term-vars will be checked for equality and dropped, or assumed to the rhs value

: (solve1) ( subst problem var term -- subst )
    {
        { [ 2dup [ __? ] either? ] [ 2drop (solve) ] }
        ! { [ 2dup defined-equal? ] [ 2drop (solve) ] }
        { [ over atom-match? ] [ dup ground-value? [ [ var>> ] dip (solve1) ] [ 4drop f ] if ] }
        { [ dup atom-match? ] [ over ground-value? [ var>> (solve1) ] [ 4drop f ] if ] }
        { [ over valid-term-var? ] [ 2dup = [ 2drop (solve) ] [ elim ] if ] }
        { [ dup valid-term-var? ] [ swap elim ] }
        { [ 2dup = ] [ 2drop (solve) ] }
        [ decompose [ zip prepend ] [ 2drop ] if (solve) ]
    } cond ; inline recursive

: (solve) ( subst problem -- subst )
    [ unclip first2
      [ ?ground-value ] bi@
      (solve1) ] unless-empty ; inline recursive

ERROR: recursive-term-error subst problem var term ;
SINGLETON: +keep+
SYMBOL: on-recursive-term
: recursive-term ( subst problem var term -- subst )
    on-recursive-term get
    [ dup +keep+? [ 3drop (solve) ] [ nip elim ] if ]
    [ recursive-term-error ] if* ;

: elim ( subst problem var term -- subst )
    2dup occurs? [ recursive-term ]
    [ swap associate
      [ [ [ lift ] curry map-values ] keep assoc-union ]
      [ [ [ lift ] curry bi@ ] curry assoc-map ] bi-curry bi*
      (solve) ] if ;

: solve ( subst problem -- subst )
    [ (solve) ]
    [ dup incompatible-terms? [ 3drop f ] [ rethrow ] if ]
    recover ; inline

: solve-problem ( problem -- subst )
    H{ } clone swap solve ;

: solve-next ( subst problem -- subst )
    swap >alist append solve-problem ; inline

: solve-eq ( term1 term2 -- subst )
    2array 1array solve-problem ; inline

: solve-eq-with ( subst term1 term2 -- subst )
    2array 1array solve-next ; inline

: solve-in ( term eqns -- term subst )
    solve-problem [ lift ] keep ; inline

: no-var-restrictions ( quot -- )
    valid-match-vars swap with-variable-off ; inline

! Only make parts of vars fresh
: fresh-with ( term vars -- term )
    [ clone ] dip
    [ dup name>> uvar <term-var> ] H{ } map>assoc
    valid-match-vars [ lift ] with-variable-off ;

! Only term vars!
: fresh ( term -- term )
    dup term-vars fresh-with ;

! * Proper Terms
TUPLE: term parts ;
SYNTAX: T( \ ) parse-until >array term boa suffix! ;
M: term pprint* 10 nesting-limit [ pprint-object ] with-variable ;
M: term pprint-delims drop \ T( \ ) ;
M: term >pprint-sequence parts>> ;

! * Interface

! Interface for builtin solving
! NOTE: This tests alpha-equality
: test-eq ( lhs rhs -- ? )
    solve-eq { [  ] [ assoc-empty? ] } 1&& ;
