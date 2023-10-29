USING: accessors arrays assocs assocs.extras classes classes.tuple
colors.constants combinators combinators.short-circuit continuations
disjoint-sets disjoint-sets.private generalizations graphs hash-sets hashtables
hashtables.identity io.styles kernel lexer make match math math.combinatorics
math.order math.parser namespaces parser prettyprint.backend prettyprint.config
prettyprint.custom prettyprint.sections quotations sequences sets slots.private
sorting strings types.util unicode words words.symbol ;

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
    [ IH{ } clone var-context boa ] dip
    with-var-context
    ; inline

! : with-new-eq-scope ( quot -- )
!     <eq-disjoint-set> swap with-eq-scope ; inline

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

! Keep track of ground terms for equivalence classes
! This needs to be somewhat fast.  Also, it should return
! a canonical representation.
! Return flag indicating whether the variable was changed
: ?ground-value ( var -- val/key )
    dup term-var?
    [ defined-equalities
      [
          representative
          defined-ground-values ?at drop
      ] when*
    ] when ; inline

! Return flag indicating whether the variable was changed
: ?ground-value? ( var -- val/key changed )
    [ ?ground-value ] keep over eq? not ; inline

! The idea is to make sure to compute the hash-code of the things
! actually represented by it, so they can be used as keys without having to
! perform a lift operation?
! NOTE: Care must be taken that depth limits are treated similarly if expansion has happened?
! Approach: if we did resolve to a ground-value, re-increase the depth counter as if
! nothing happened.

! NOTE: Slow! better not rely on this!
! M: term-var hashcode*
!     ! term-var-hashcode* ; inline
!     ?ground-value dup term-var? [ call-next-method ]
!     [ [ 1 + ] dip [ hashcode* ] recursive-hashcode ] if ; inline


: define-term-var ( name -- )
    create-word-in [ define-symbol ]
    [ t "term-var" set-word-prop ]
    bi ;

PREDICATE: known-term-var < term-var
    defined-equalities [ disjoint-set-member? ] [ drop f ] if* ;
PREDICATE: unresolved-term-var < known-term-var
    defined-ground-values key? ;

M: term-var pprint*
    name>> H{ { foreground COLOR: solarized-blue } } styled-text ;

M: known-term-var pprint*
    name>> H{ { foreground COLOR: solarized-cyan } } styled-text ;

M: unresolved-term-var pprint*
    name>> H{ { foreground COLOR: solarized-red } } styled-text ;


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
M: term-var child-elts* ?ground-value
    dup term-var? [ drop f ] [ 1array ] if ;

GENERIC: vars* ( obj -- )
M: object vars* drop ;
M: match-var vars* , ;
M: term-var vars* ?ground-value
    dup term-var? [ , ] [ drop ] if ;
M: wrapper vars* wrapped>> vars* ;
! M: sequence vars* [ vars* ] each ;
! M: tuple vars* tuple-slots vars* ;

: vars ( obj -- seq )
    [ [ [ vars* ] [ child-elts* ] bi ] closure drop ] { } make
    members ; inline

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

! XXX This is SOOOOOOOOO expensive, check-recursive-terms an the lifting both...
: update-ground-values! ( assoc -- )
    [ [ keys ] keep [ [ f lift ] change-at ] curry each ]
    [
        ! check-recursive-terms
        drop
    ] bi
    ; inline

:: define-ground-value ( var value ds -- )
    value f lift :> value
    var ds
    representative defined-ground-values
    [
        [| old | old [ old value = [ old ] [ old value ground-value-contradiction ] if ]
         [ value ] if
        ] change-at
    ] [
        ! update-ground-values!
        drop
    ] bi
    ; inline

: ground-value? ( obj -- ? )
    vars empty? ; inline

: maybe-update-ground-values ( a b -- )
    2drop defined-ground-values update-ground-values! ;
    ! [ defined-ground-values ] 2dip pick [ key? ] curry either?
    ! [ update-ground-values ground-values set ] [ drop ] if ;

! Main entry point for atoms
:: assume-equal ( a b -- )
    defined-equalities :> ds
    { { [ a b [ term-var? ] both? ] [ a b [ ds equate ] [
                                          ! maybe-update-ground-values
                                          2drop
                                      ] 2bi ] }
      { [ a term-var? ] [ a b ds define-ground-value  ] }
      { [ b term-var? ] [ b a ds define-ground-value  ] }
      [ a b "trying to make something other than term vars equal" 3array throw ]
    } cond ;

! * Unification
! Baader/Nipkow
! FIXME: this probably needs to be rewritten to never clone stuff that does not contain variables
! to make sure that eq? checks on values are stable over e.g. creating fresh effects
! Either check subterm for variables, or first deconstruct while keeping track of where rebuilding
! needs to take place
! Maybe do this efficiently with continuations?  Pass a continuation down which to invoke if the element has been changed.
! E.g. for a sequence:
! Create a quotation, which when invoked with one arg, prefixes the supplied value to the REST OF THE SEQUENCE.  Pass that continuation down.
GENERIC: subst ( modified? assoc term -- modified? assoc term )
SINGLETON: __

! This is for matching ground-terms only, basically as if expecting something that can be wrapped
TUPLE: atom-match { var read-only } ;
C: <atom-match> atom-match

! This is for matching variables only
TUPLE: var-match { var read-only } ;
C: <var-match> var-match

! This is for matching certain factor instances only
TUPLE: class-match { class read-only } { var read-only } ;
C: <class-match> class-match

! Adding bindings inside matcher structure
TUPLE: bind-match { var read-only } { obj read-only } ;
C: <bind-match> bind-match

SYMBOL: in-quotation?
SYMBOL: quote-substitution
SYMBOL: current-subst
! ! SYMBOL: keep-ground-values
! SYMBOL: did-subst

! : when-has-vars ( assoc term quot -- assoc term )
!     2over vars [ swap key? ] with any?
!     [ call( a term -- a term ) ] [ drop ] if ; inline

! :: maybe-unmodified ( assoc term quot -- assoc term )
!     keep-ground-values get [ term ground-value? ] [ f ] if
!     [ assoc term ]
!     [ assoc term quot call( x x -- x x ) ] if ; inline
! :: maybe-unmodified ( assoc term quot -- assoc term )
!     [ did-subst off
!       assoc term quot call( x x -- x x )
!       did-subst get
!     ] with-scope :> ( assoc new-term modified? )
!     modified? dup did-subst set
!     [ new-term ] [ term ] if assoc swap ;
:: maybe-unmodified ( mod assoc term quot -- mod assoc term )
    f assoc term quot call( x x x -- x x x ) :> ( new-mod assoc new-term )
    ! mod assoc term quot call( x x x -- x x x ) :> ( new-mod assoc new-term )
    new-mod mod or assoc
    new-mod new-term term ? ;

: quoting-substitution ( quot -- )
    [ quote-substitution get in-quotation? ] dip with-variable ; inline
: no-quoting ( quot -- )
    in-quotation? swap with-variable-off ; inline

M: object subst ;
M: term-var subst
    over ?at
    -rot [ or ] 2dip
    ?ground-value?
    -rot [ or ] 2dip
    dup { [ drop in-quotation? get ] [ word? ] [ { [ deferred? ] [ match-var? not ] } 1|| ] } 1&& [ <wrapper> ] when
    ;

M: match-var subst
    over ?at -rot [ or ] 2dip ;

M: quotation subst
    [ [ [ subst ] map ] quoting-substitution ] maybe-unmodified ;

M: sequence subst
    [ [ [ subst ] map ] no-quoting ] maybe-unmodified ;

! ! TODO: assess whether this is 1. sound, 2. necessary at all?
! ! As an exception, we don't rebuild vectors!
! M: vector subst
!     [ [ subst ] map! ] no-quoting ;

<PRIVATE
: num-slots ( tup -- n )
    1 slot second ; inline
PRIVATE>

: tuple-subst ( mod assoc term -- mod assoc term )
    [ clone dup num-slots
    [| i | i 2 + :> n
     [ n slot subst ]
     [ n set-slot ]
     [  ] tri
    ] each-integer ] maybe-unmodified ; inline

M: curried subst
    [ [ obj>> [ subst ] no-quoting ]
      [ quot>> [ subst ] quoting-substitution ] bi
      curried boa ] maybe-unmodified ;

M: composed subst
    [ tuple-subst ] quoting-substitution ;

M: tuple subst
    [ tuple-subst ] no-quoting ;

M: wrapper subst wrapped>>
    in-quotation? [
        [ subst ] maybe-unmodified
    ] with-variable-off
    <wrapper> ;

! If substitution result is ground-value, return that.  Otherwise, re-wrap
! as atom-match.
M: atom-match subst
    var>> subst dup ground-value? [ <atom-match> ] unless ;

! TODO: do we need to check the instance here? The substitution should
! only contain a match for the content if the class has been checked, no?
M:: class-match subst ( mod asc term -- mod asc term )
    mod asc term var>> subst :> newterm
    newterm ground-value? [ newterm ]
    [ term class>> newterm <class-match> ] if ;

: lift ( term subst -- term )
    f spin subst 2nip ;

GENERIC: occurs? ( var term -- ? )
M: object occurs? 2drop f ;
M: match-var occurs? = ;
M: term-var occurs? eq? ;
M: sequence occurs? [ occurs? ] with any? ;
M: tuple occurs? tuple-slots occurs? ;

! The whole idea of matching structure kind of conflicts with matching pointer
! values...
ERROR: rebuilds-identity-tuple term ;
M: identity-tuple subst rebuilds-identity-tuple ;

! NOTE: basically a copy of eq-wrapper of bootstrap.image.private
TUPLE: eq-wrap { obj read-only } ;
C: <eq-wrap> eq-wrap

ERROR: parsing-non-eq-testable-literal obj ;
: check-literal-eq-wrap-object ( x -- x )
    dup union{ fixnum word term-var } instance?
    [ parsing-non-eq-testable-literal ] unless ; inline
SYNTAX: Eq{ scan-object "}" expect
    check-literal-eq-wrap-object <eq-wrap> suffix! ;

! Do not touch anything inside here
! eq-wrappers are equal if their objects are eq.
! eq-wraps are equal if either their objects are eq, but on the term-var level.
! So as long as two eq-wraps which are supposed to be eq are always constructed with the same term-var,
! that coundition should be fulfilled?
M: eq-wrap equal? over eq-wrap? [ [ obj>> ] bi@ eq? ] [ 2drop f ] if ;
M: eq-wrap hashcode* nip obj>> identity-hashcode ;
! M: eq-wrap subst dup obj>> term-var? [ call-next-method ] when  ;
! M: eq-wrap subst rebuilds-identity-tuple ;
M: eq-wrap subst ;
M: eq-wrap pprint* pprint-object ;
M: eq-wrap pprint-delims drop \ Eq{ \ } ;
M: eq-wrap >pprint-sequence obj>> 1array ;


ERROR: incompatible-terms term1 term2 ;

SYNTAX: A{ scan-object "}" expect <atom-match> suffix! ;
M: atom-match pprint* pprint-object ;
M: atom-match pprint-delims drop \ A{ \ } ;
M: atom-match >pprint-sequence var>> 1array ;

SYNTAX: M{ scan-object "}" expect <var-match> suffix! ;
M: var-match pprint* pprint-object ;
M: var-match pprint-delims drop \ M{ \ } ;
M: var-match >pprint-sequence var>> 1array ;

SYNTAX: Is( scan-object classoid check-instance scan-object ")" expect <class-match> suffix! ;

M: class-match pprint* pprint-object ;
M: class-match pprint-delims drop \ Is( \ ) ;
M: class-match >pprint-sequence [ class>> ] [ var>> ] bi 2array ;

SYNTAX: Bind( scan-object term-var check-instance scan-object ")" expect <bind-match> suffix! ;
M: bind-match pprint* pprint-object ;
M: bind-match pprint-delims drop \ Bind( \ ) ;
M: bind-match >pprint-sequence tuple-slots ;

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
: decompose-callable ( term1 term2 -- terms1 terms2 cont? )
    2dup [ callable? ] both?
    [ 2dup [ length ] same? ] [ f ] if ; inline
M: curried decompose-left decompose-callable ;
M: curried decompose-right decompose-callable ;
M: composed decompose-left decompose-callable ;
M: composed decompose-right decompose-callable ;
M: quotation decompose-left decompose-callable ;
M: quotation decompose-right decompose-callable ;

M: bind-match decompose-right "bind-match on rhs" throw ;
! lhs-seq: { var obj } rhs-seq: { term term }
M:: bind-match decompose-left ( bmatch term -- terms1 terms2 cont? )
    bmatch var>> bmatch obj>> 2array
    term dup 2array t ;
TUPLE: match-set elements ;
C: <match-set> match-set
: make-match-sets ( set -- seq signature )
    members [ ?ground-value dup term-var? [ "term vars in match set not supported" throw ] when class-of ] collect-by sort-keys
    [ [ <match-set> ] map-values ] [ [ length ] map-values >alist ] bi ;
M: sets:set decompose-right
    2dup { [ [ class-of ] same? ] [ [ cardinality ] same? ] } 2&&
    [ [ make-match-sets ] bi@ swapd = ]
    [ f ] if ;

: decompose ( term1 term2 -- term1 term2 cont? )
    {
        [
            { [ decompose-left ] [ decompose-right ] } 0||
            [ 2dup eq? [ f ] [ incompatible-terms ] if ] unless*
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

! If set, only an isomporphic solution is accepted during solving
SYMBOL: solve-isomorphic-mode?

! TODO: put that into the subst checking early!
: isomorphic-solution? ( subst -- ? )
    { [ [ [ term-var? ] both? ] assoc-all? ]
        [ values all-unique? ] } 1&& ; inline

: check-solution ( subst -- ? )
    [ solve-isomorphic-mode? get
      [ dup isomorphic-solution?
        [ drop f ] unless
      ] when
    ]
    [ f ] if*
    ; inline

ERROR: imbalanced-match-sets-after-pruning elts1 elts2 ;
! NOTE: assume matching signatures here
! Friggin expensive! Complexity is n1! x n2! x ... nk!
! In the cardinalities of the partitioned subsets
! Strategy: Pin down set1, try all permutations of set2
! CAVEAT: will not work if variables need to match set elements! (really?)
! Semantic restriction: If the elements are present in both sets, they are pruned
! in hopes of getting the smallest unifier...
: prune-match-sets ( set1 set2 -- elts1 elts2 )
    [ elements>> ] bi@
    2dup [ [ match-set? ] reject ] bi@ intersect
    [ diff ] curry bi@
    2dup [ length ] same? [ imbalanced-match-sets-after-pruning ] unless
    ;

: compatible-match-sets? ( set1 set2 -- ? )
    [ elements>> length ] same? ;

: solve-match-set ( subst problem set1 set2 -- subst )
    [let f :> sol!
     2dup compatible-match-sets?
     [
         prune-match-sets
         [ 2array prefix [ (solve)
                           check-solution
                           dup [ sol! ] when* ]
           [ dup incompatible-terms? [ 3drop f ] [ rethrow ] if ] recover
         ] 3 nwith find-permutation drop
     ] [ 4drop ] if
     sol
    ] ; inline recursive

! TODO: check if we need the deref check on lhs!
: check-class-match ( lhs class-match -- ? )
    [ ?ground-value ] dip
    ! over valid-term-var? [ 2drop f ]
    over term-var? [ 2drop f ]
    [ class>> instance? ] if ; inline

! NOTE:
! - rhs term-vars will always be assumed to the lhs value
! - lhs term-vars will be checked for equality and dropped, or assumed to the rhs value

! XXX There seems to be a bug with Hash set equality comparison?  Either the
! complexity is abysmal, or there is something wrong...
: (solve1) ( subst problem var term -- subst )
    {
        { [ 2dup [ __? ] either? ] [ 2drop (solve) ] }
        ! { [ 2dup defined-equal? ] [ 2drop (solve) ] }
        { [ 2dup [ eq-wrap? ] both? ] [ 2dup = [ 2drop (solve) ] [ 4drop f ] if ] }
        { [ over atom-match? ] [ dup ground-value? [ [ var>> ] dip (solve1) ] [ 4drop f ] if ] }
        { [ dup atom-match? ] [ over ground-value? [ var>> (solve1) ] [ 4drop f ] if ] }
        { [ over class-match? ] [ 2dup swap check-class-match [ [ var>> ] dip (solve1) ] [ 4drop f ] if ] }
        { [ dup class-match? ] [ "class match on rhs" throw ] }
        { [ over var-match? ] [ dup term-var? [ [ var>> ] dip (solve1) ] [ 4drop f ] if ] }
        { [ dup var-match? ] [ over term-var? [ var>> (solve1) ] [ 4drop f ] if ] }
        { [ over valid-term-var? ] [ 2dup = [ 2drop (solve) ] [ elim ] if ] }
        { [ dup valid-term-var? ] [ swap elim ] }
        ! { [ dup hash-set? [ f ] [ 2dup = ] if ] [ 2drop (solve) ] }
        { [ dup hash-set? [ f ] [ 2dup eq? ] if ] [ 2drop (solve) ] }
        { [ 2dup [ match-set? ] both? ] [ solve-match-set ] }
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

: isomorphic? ( term1 term2  -- ? )
    [ solve-isomorphic-mode? on
      solve-eq ] no-var-restrictions
    [ isomorphic-solution? ] [ f ] if* ;

: lift* ( term subst -- term )
    [ lift ] no-var-restrictions ;

! Only make parts of vars fresh
: fresh-with ( term vars -- term )
    [ clone ] dip
    [ dup name>> uvar <term-var> ] H{ } map>assoc
    valid-match-vars [ lift ] with-variable-off ;

! Only term vars!
: fresh ( term -- term )
    dup term-vars fresh-with ;

: fresh-without ( term vars -- term )
    over term-vars swap diff fresh-with ;

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
