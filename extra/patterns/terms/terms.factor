USING: assocs classes combinators combinators.short-circuit hashtables kernel
lists match math sequences sets typed ;

IN: patterns.terms

! TUPLE: compound head args

! TUPLE: app left right ;
! C: <app> app

! VARIANT: pattern-term
!     psym: { name }
!     pcons: { obj }
!     ;

! UNION: pattern pattern-term app ;
! PREDICATE: papp < app [ left>> ] [ right>> ] bi [ pattern? ] both? ;

! VARIANT: term-term
!     tvar: { name }
!     tcons: { obj }
!     tcase: { { pattern pattern } { body term } }
!     ;

! UNION: term term-term app ;
! PREDICATE: tapp < app [ left>> ] [ right>> ] bi [ term? ] both? ;

! UNION: data class tuple ;

! ! VARIANT: match-res
! !     nomatch
! !     none
! !     undefined
! !     some: { subst }
! !     ;

! Factorization protocol
MIXIN: app-term
GENERIC: left/right ( app -- left right )
GENERIC: head-term ( term -- term )



INSTANCE: list app-term
M: list left/right uncons ;
M: list head-term car ;
! Head sequence
PREDICATE: app-seq < sequence length 1 > ;
INSTANCE: app-seq app-term
! M: app-seq left/right 2 cut-slice ;
: maybe-unseq ( seq -- term )
    dup length 1 = [ first ] when ;
M: app-seq head-term first ;
M: app-seq left/right
    unclip-last-slice
    [ maybe-unseq ] dip ;

TUPLE: pcase pattern body ;
C: <pcase> pcase

SINGLETONS: undefined none ;
UNION: match-result assoc undefined none ;

! TYPED: matching ( u: term p: pattern -- result )
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

SINGLETON: nomatch
TUPLE: subst-app subst term ;
C: <subst-app> subst-app
UNION: match-app subst-app nomatch ;
GENERIC#: apply-match 1 ( match-result term -- match-app )
M: assoc apply-match <subst-app> ;
M: none apply-match 2drop nomatch ;

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

: do-match ( pattern term -- result )
    swap [ pattern>> ] [ body>> ] bi [ matching ] dip apply-match ;
