USING: accessors assocs combinators combinators.short-circuit continuations
hashtables kernel match namespaces patterns.terms sets typed types.util ;

IN: patterns.static

FROM: patterns.terms => undefined ;

! * Static pattern calculus

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
: destructure-match ( compound-term app-term -- result )
    [ left/right ] bi@ swapd
    [ matching ] 2bi@ match-disjoint-union ;
M: app-term matching
    over compound? [ destructure-match ]
    [ call-next-method ] if ;
M: object matching
    drop matchable? none undefined ? ;

TYPED: do-match-rule ( pattern: pcase term -- result: match-app )
    swap [ pattern>> ] [ body>> ] bi [ matching ] dip match-rule ;

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
! M: subst-app cleanup-match t ;
M: fixpoint-subst-app cleanup-match
    term>> f ;

: reject-fixpoint ( app-term app-term' ? -- app-term ? )
    [ tuck = not ]
    [ nip f ] if ;

: spc-reduce-redex ( term -- term ?  )
    dup
    [ left/right [ >pattern ] dip do-match-rule cleanup-match ]
    [ dup undefined-match? [ drop f ] [ rethrow ] if ] recover
    reject-fixpoint ;

: reduce-all ( term -- term ? )
    f swap [ spc-reduce-step tuck [ or ] 2dip ] co-loop
    swap ;

: reduce-app ( left right -- left right ? )
    [ reduce-all ] bi@ swapd or ;

TYPED: distribute-reduction ( term: app-term -- term ? )
    dup left/right reduce-app
    [ rot new-app-term t ]
    [ 2drop f ] if ;

M: sp-redex spc-reduce-step
    [ distribute-reduction ] co-loop
    spc-reduce-redex ;

M: app-term spc-reduce-step
    distribute-reduction ;

M: object spc-reduce-step f ;

: spc-reduce ( term -- term )
    reduce-all drop ;
    ! [ spc-reduce-step ] loop ;
