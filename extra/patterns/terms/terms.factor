USING: accessors arrays assocs classes combinators combinators.short-circuit
continuations hashtables kernel lists match math namespaces parser
prettyprint.custom sequences sets typed types.util vectors words words.constant
;

IN: patterns.terms

FROM: syntax => _ ;
! Factorization protocol
MIXIN: app-term
GENERIC: left/right ( app -- left right )
GENERIC: head-term ( term -- term )
GENERIC: new-app-term ( left right exemplar -- app-term )

INSTANCE: list app-term
M: list left/right uncons ;
M: list head-term car ;
M: cons-state new-app-term drop
    cons ;

! Head sequence
UNION: array-like array vector slice ;
PREDICATE: app-seq < array-like length 1 > ;
PREDICATE: head-seq < array-like length 1 = ;
INSTANCE: app-seq app-term
GENERIC: maybe-unseq ( seq -- term )
M: head-seq maybe-unseq first ;
M: object maybe-unseq ;
M: app-seq head-term first ;
M: app-seq left/right
    unclip-last-slice
    [ maybe-unseq ] dip ;
GENERIC: maybe-seq ( obj -- seq )

M: array-like maybe-seq ;
M: object maybe-seq 1array ;
M: app-seq new-app-term
    '[ maybe-seq _ like ] dip suffix ;

SINGLETON: nomatch

: <psym> ( name -- pattern-symbol )
    uvar <uninterned-word> [ t "pattern-symbol" set-word-prop ] keep ;

PREDICATE: pattern-symbol < word "pattern-symbol" word-prop? ;
INSTANCE: pattern-symbol match-var


TUPLE: pcase pattern body ;
C: <pcase> pcase

SYMBOL: ->
SYNTAX: P{ -> parse-until \ } parse-until [ maybe-unseq ] bi@ <pcase> suffix! ;
M: pcase pprint* pprint-object ;
M: pcase pprint-delims drop \ P{ \ } ;
M: pcase >pprint-sequence
    [ pattern>> ] [ body>> ] bi
    [ maybe-seq ] bi@ { -> } glue ;

! TUPLE: special-case pcase default ;
! C: <special-case> special-case
! Cond structure
! : <extension> ( cases default -- case )
!     [ <reversed> ] dip
!     [ first2 <pcase> swap <special-case> ] reduce ;

:: <special-case> ( p s r -- term )
    "x" <psym> :> x
    "y" <psym> :> y
    "z" <psym> :> z
    x
    { nomatch y } y <pcase>
    p z { nomatch s } <pcase> <pcase> x { r x } 3array
    2array <pcase> ;

: <extension> ( cases default -- case )
    [ <reversed> ] dip
    [ first2 rot <special-case> ] reduce ;

SINGLETONS: undefined none ;
UNION: match-result assoc undefined none ;

PREDICATE: constructor < word match-var? not ;

PREDICATE: compound < app-term head-term constructor? ;
UNION: data constructor compound ;
UNION: matchable data pcase ;

TYPED: disjoint-domains? ( s1: assoc s2: assoc -- ? )
    [ keys ] bi@ intersects? not ;

TYPED: match-disjoint-union ( m1: match-result m2: match-result -- m: match-result )
    {
        { [ 2dup [ undefined? ] either? ] [ 2drop undefined ] }
        { [ 2dup { [ [ assoc? ] both? ] [ disjoint-domains? ] } 2&& ]
          [ assoc-union ] }
        [ 2drop none ]
    } cond ;

TUPLE: subst-app subst term ;
C: <subst-app> subst-app
UNION: match-app subst-app nomatch ;
GENERIC#: match-rule 1 ( match-result term -- match-app )
M: assoc match-rule <subst-app> ;
M: none match-rule 2drop nomatch ;
ERROR: undefined-match term ;
M: undefined match-rule undefined-match ;

GENERIC: matching ( term pattern -- result )
M: match-var matching
    associate ;
M: constructor matching
    2dup = [ 2drop f ]
    [ call-next-method ] if ;
: destructure-match ( compound-term compound-pattern -- result )
    [ left/right ] bi@ swapd
    [ matching ] 2bi@ match-disjoint-union ;
M: compound matching
    over compound? [ destructure-match ]
    [ call-next-method ] if ;
M: object matching
    drop matchable? none undefined ? ;

TYPED: do-match-rule ( pattern: pcase term -- result: match-app )
    swap [ pattern>> ] [ body>> ] bi [ matching ] dip match-rule ;

PREDICATE: pattern-def < constant "constant" word-prop pcase? ;
UNION: pattern-case pattern-def pcase ;
GENERIC: >pattern ( obj -- obj/pattern )
M: object >pattern ;
M: pattern-def >pattern "constant" word-prop ;


PREDICATE: sp-redex < app-term left/right drop pattern-case? ;
! Static reduction
GENERIC: spc-reduce-step ( term -- term ? )
GENERIC#: cleanup-match 1 ( match-app ? -- term ? )
M: match-app cleanup-match ;
PREDICATE: fixpoint-subst < assoc
    { [ assoc-empty? not ] [ [ = ] assoc-all? ] } 1&& ;
PREDICATE: fixpoint-subst-app < subst-app subst>> fixpoint-subst? ;

M: fixpoint-subst-app cleanup-match
    drop term>> f ;
M: subst-app cleanup-match drop
    [ term>> ] [ subst>> ] bi
    [ replace-partial? [ replace-patterns ] with-variable-on ] with-variables t ;

M: sp-redex spc-reduce-step
    [ left/right [ >pattern ] dip do-match-rule t
      cleanup-match ]
    [ dup undefined-match? [ drop f ] [ rethrow ] if ] recover ;

: reduce-all ( term -- term ? )
    f swap [ spc-reduce-step tuck [ or ] 2dip ] loop
    swap ;

: reduce-app ( left right -- left right ? )
    [ reduce-all ] bi@ swapd or ;

M: app-term spc-reduce-step
    dup left/right reduce-app
    [ rot new-app-term t ]
    [ 2drop f ] if ;

M: object spc-reduce-step f ;

: spc-reduce ( term -- term )
    [ spc-reduce-step ] loop ;

