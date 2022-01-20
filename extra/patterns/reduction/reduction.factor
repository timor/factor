USING: accessors assocs combinators.short-circuit continuations kernel match
namespaces patterns.terms typed types.util ;

IN: patterns.reduction


GENERIC#: do-match-rule 1 ( pattern term -- result: match-app )

PREDICATE: pc-redex < app-term left/right drop reduction-defined? ;
! Static reduction
GENERIC: pc-reduce-step ( term -- term ? )
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
    [ tuck [ = ] with-alpha= not ]
    [ nip f ] if ;

: pc-reduce-redex ( term -- term ?  )
    dup
    [ left/right [ >pattern ] dip do-match-rule cleanup-match ]
    [ dup undefined-match? [ drop f ] [ rethrow ] if ] recover
    reject-fixpoint ;

: reduce-all ( term -- term ? )
    f swap [ pc-reduce-step tuck [ or ] 2dip ] co-loop
    swap ;

: reduce-app ( left right -- left right ? )
    [ reduce-all ] bi@ swapd or ;

TYPED: distribute-reduction ( term: app-term -- term ? )
    dup left/right reduce-app
    [ rot new-app-term t ]
    [ 2drop f ] if ;

M: pc-redex pc-reduce-step
    [ distribute-reduction ] co-loop
    pc-reduce-redex ;

M: app-term pc-reduce-step
    distribute-reduction ;

M: object pc-reduce-step f ;

: pc-reduce ( term -- term )
    reduce-all drop ;
    ! [ pc-reduce-step ] loop ;
