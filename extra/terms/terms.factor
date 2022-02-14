USING: accessors arrays assocs assocs.extras classes classes.tuple
colors.constants combinators combinators.short-circuit continuations
disjoint-sets disjoint-sets.private hashtables hashtables.identity io.styles
kernel lexer make match math math.order math.parser namespaces parser
prettyprint.custom prettyprint.sections quotations sequences sets strings
types.util unicode words words.symbol ;

IN: terms

FROM: syntax => _ ;

! * Specialized to not cause loops
TUPLE: eq-disjoint-set < tuple
    { parents identity-hashtable read-only }
    { ranks identity-hashtable read-only }
    { counts identity-hashtable read-only } ;

: <eq-disjoint-set> ( -- obj )
    IH{ } clone IH{ } clone IH{ } clone eq-disjoint-set boa ;

<PRIVATE
SYMBOL: no-defined-equalities
PRIVATE>
! M: eq-disjoint-set equiv?
!     no-defined-equalities [ call-next-method ] with-variable-on ; inline
M: eq-disjoint-set equiv?
    representatives eq? ;
    ! no-defined-equalities [ call-next-method ] with-variable-on ; inline
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

! * State

SYMBOL: substitute-representatives?
SYMBOL: defined-equalities-ds
: defined-equalities ( -- ds )
    defined-equalities-ds get-global ; inline

<PRIVATE
SYMBOL: eq-stack
PRIVATE>

! :: defined-equal? ( v1 v2 -- ? )
!     defined-equalities
!     [| ds |
!      v1 v2 [ ds disjoint-set-member? ] both?
!      [ v1 v2 ds equiv? ] [ f ] if
!     ] [ f ] if* ; inline

! TODO: this is expensive!
SYMBOL: check-vars?
: check-vars ( v1 v2 -- )
    [ defined-equalities disjoint-set-member? ] both?
    [ "nope" throw ] unless ;

: safe-equiv? ( v1 v2 ds -- ? )
    ! 2over check-vars
    equiv? ; inline

: defined-equal? ( v1 v2 -- ? )
    ! no-defined-equalities get
    ! [ 2drop f ] [
        defined-equalities
    [
        ! check-vars? get [ 2over check-vars ] when
        safe-equiv? ] [ 2drop f ] if*
    ! ] if
    ; inline

: check-integrity ( -- )
    defined-equalities parents>> [ nip ] assoc-all?
    [ "Bad" throw ] unless ;

: with-eq-scope ( disjoint-set quot -- )
    '[ defined-equalities
       eq-stack [ swap suffix ] change
       ! [ clone ] [ <eq-disjoint-set> ] if* defined-equalities-ds set-global
       _ defined-equalities-ds set-global
       [ @ ]
       check-integrity
       [ eq-stack [ unclip swap ] change
         defined-equalities-ds set-global ] finally
    ] with-scope ; inline

DEFER: vars
: with-term-vars ( obj quot -- )
    [ vars <eq-disjoint-set> [ add-atoms ] keep ] dip
    with-eq-scope ; inline

: import-vars ( seq -- )
    defined-equalities add-atoms ;
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

: umatchvar ( name -- word )
    usym dup
    t "match-var" set-word-prop ;

! * Term variables
PREDICATE: term-var < word "term-var" word-prop ;
INSTANCE: term-var match-var


M: term-var equal?
    over term-var?
    [ defined-equal? ] [ 2drop f ] if ;
    ! { [ eq? ]
    !   [ defined-equal? ] } 2|| ; inline

: define-term-var ( name -- )
    create-word-in [ define-symbol ]
    [ t "term-var" set-word-prop ]
    [ t "termplate" set-word-prop ]
    tri ;

M: term-var pprint*
    name>> H{ { foreground COLOR: solarized-blue } } styled-text ;

M: term-var reset-word
    [ call-next-method ]
    [ f "term-var" set-word-prop ]
    [ "template" remove-word-prop ] tri
    ;

SYNTAX: TERM-VARS: ";" [ define-term-var ] each-token ;

: <term-var> ( name -- var )
    <uninterned-word>
    dup t "term-var" set-word-prop
    dup defined-equalities add-atom ;

GENERIC: vars* ( obj -- )
M: object vars* drop ;
M: match-var vars* , ;
M: sequence vars* [ vars* ] each ;
M: tuple vars* tuple-slots vars* ;

: vars ( obj -- seq )
    [ vars* ] { } make ;


! * Ground Values

SYMBOL: ground-values

: maybe-add-atom ( x ds -- )
    2dup disjoint-set-member?
    [ 2drop ] [ add-atom ] if ; inline

ERROR: ground-value-contradiction old value ;

:: define-ground-value ( var value ds -- )
    var ds 2dup maybe-add-atom
    representative ground-values get
    [| old | old [ old value = [ old ] [ old value ground-value-contradiction ] if ]
     [ value ] if
    ] change-at ;

: ground-value? ( obj -- ? )
    vars empty? ; inline

: maybe-define-ground-value ( v1 v2 ds -- )
    ! over ground-value? not [ swapd ] when
    ! over ground-value? not [ 3drop ] [
    over match-var? [ swapd ] when
    over match-var? [ 3drop ] [
        define-ground-value
    ] if ; inline

! Keep track of ground terms for equivalence classes
: ?ground-value ( var -- val/key )
    ground-values get ?at drop ;

: assume-equal ( a b -- )
    defined-equalities
    [
        2over [ match-var? ] either?
        [
            {
                [ nipd maybe-add-atom ]
                [ nip maybe-add-atom ]
                [ equate ]
            }
            3cleave
        ] [ 3drop ] if
    ] [ maybe-define-ground-value ] 3bi ;


! * Unification
! Baader/Nipkow
GENERIC: subst ( term -- term )
SINGLETON: __

SYMBOL: in-quotation?
SYMBOL: current-subst
: get-current-subst ( obj -- obj/f )
    current-subst get at ;

: ?representative ( var -- var )
    { [ defined-equalities representative ] [  ] } 1||
    ground-values get ?at drop
    ; inline

: var-subst ( obj -- obj/f )
    ! substitute-representatives? get
    t
    [ ?representative ] when
    [ get-current-subst
      dup { [ word? ] [ { [ deferred? ] [ match-var? not ] } 1|| ] [ drop in-quotation? get ] } 1&& [ <wrapper> ] when
    ] keep
    or ; inline


! M: object subst var-subst ;
M: object subst ;
M: match-var subst var-subst ;
M: sequence subst
    dup quotation?
    in-quotation? [ [ subst ] map ] with-variable ;
M: callable subst
    in-quotation? [ call-next-method ] with-variable-on ;
M: tuple subst tuple>array subst >tuple ;
M: wrapper subst wrapped>>
    in-quotation? [ subst ] with-variable-off
    <wrapper> ;

: lift ( term subst -- term )
    current-subst [ subst ] with-variable ;

GENERIC: occurs? ( var term -- ? )
M: object occurs? 2drop f ;
M: match-var occurs? = ;
M: sequence occurs? [ occurs? ] with any? ;
M: tuple occurs? tuple-slots occurs? ;

ERROR: rebuilds-identity-tuple term ;
M: identity-tuple subst rebuilds-identity-tuple ;

ERROR: incompatible-terms term1 term2 ;

! Tried first
GENERIC#: decompose-left 1 ( term1 term2 -- terms1 terms2 cont? )
GENERIC: decompose-right ( term1 term2 -- terms1 terms2 cont? )
M: object decompose-right f ;
M: object decompose-left decompose-right ;
M: tuple decompose-right
    2dup [ class-of ] same?
    [ [ tuple-slots ] bi@ t ] [ f ] if ;
M: sequence decompose-right
    2dup { [ drop sequence? ] [ [ length ] same? ] } 2&& ;

: decompose ( term1 term2 -- term1 term2 cont? )
    {
        [
            { [ decompose-left ] [ decompose-right ] } 0||
            [ 2dup = [ f ] [ incompatible-terms ] if ] unless*
        ]
    } cond ;

SYMBOL: valid-match-vars
: valid-match-var? ( var -- ? )
    dup match-var? [
        valid-match-vars get
        [ in? ] [ drop t ] if*
    ] [ drop f ] if ; inline

DEFER: elim
: (solve) ( subst problem -- subst )
    [ unclip first2
      {
          { [ 2dup [ __? ] either? ] [ 2drop (solve) ] }
          ! { [ 2dup defined-equal? ] [ 2drop (solve) ] }
          { [ over valid-match-var? ] [ 2dup = [ 2drop (solve) ] [ elim ] if ] }
          { [ dup valid-match-var? ] [ swap elim ] }
          { [ 2dup = ] [ 2drop (solve) ] }
          [ decompose [ zip prepend ] [ 2drop ] if (solve) ]
       } cond ] unless-empty ; inline recursive

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
      (solve) ] if ; inline recursive

: solve ( subst problem -- subst )
    [ (solve) ]
    [ dup incompatible-terms? [ 3drop f ] [ rethrow ] if ]
    recover ; inline

: solve-problem ( problem -- subst )
    H{ } clone swap solve ; inline

: solve-next ( subst problem -- subst )
    swap >alist append solve-problem ;

: solve-eq ( term1 term2 -- subst )
    2array 1array solve-problem ;

: solve-eq-with ( subst term1 term2 -- subst )
    2array 1array solve-next ;

: solve-in ( term eqns -- term subst )
    solve-problem [ lift ] keep ;

! * Interface

! Interface for builtin solving
! NOTE: This tests alpha-equality
: test-eq ( lhs rhs -- ? )
    solve-eq { [  ] [ assoc-empty? ] } 1&& ;
