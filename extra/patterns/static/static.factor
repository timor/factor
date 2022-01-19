USING: accessors assocs combinators combinators.short-circuit continuations
hashtables kernel match namespaces patterns.terms sets typed words
words.constant ;

IN: patterns.static

FROM: patterns.terms => undefined ;

! * Static pattern calculus

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
GENERIC: cleanup-match ( match-app -- term ? )
M: nomatch cleanup-match t ;
PREDICATE: fixpoint-subst < assoc
    { [ assoc-empty? not ] [ [ = ] assoc-all? ] } 1&& ;
PREDICATE: fixpoint-subst-app < subst-app subst>> fixpoint-subst? ;

TYPED: apply-subst ( res: match-app -- term )
    [ term>> ] [ subst>> ] bi
    [ replace-partial? [ replace-patterns ] with-variable-on ] with-variables ;

M: subst-app cleanup-match apply-subst t ;
M: fixpoint-subst-app cleanup-match
    term>> f ;

: reject-fixpoint ( app-term app-term' ? -- app-term ? )
    [ tuck = not ]
    [ nip f ] if ;

M: sp-redex spc-reduce-step
    dup
    [ left/right [ >pattern ] dip do-match-rule cleanup-match ]
    [ dup undefined-match? [ drop f ] [ rethrow ] if ] recover
    reject-fixpoint ;

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
