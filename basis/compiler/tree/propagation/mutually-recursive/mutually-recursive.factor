USING: accessors compiler.tree.propagation.info
compiler.tree.propagation.mutually-recursive.interface
compiler.tree.propagation.mutually-recursive.pruning
compiler.tree.propagation.simple fry kernel math math.intervals namespaces
sequences ;

IN: compiler.tree.propagation.mutually-recursive

! In contrast to inline-recursive combinators, this pass deals with "regular"
! recursive calls for output value info propagation for single and mutual recursion.

! * Divergent output infos

! Divergence at phi nodes from recursive call sites

! Return t if the info from the recursive call site has a lower lower bound.
: lower-bound-diverges? ( base-case-info recursive-info -- t )
    [ interval>> from>> first ] bi@ > ;

: upper-bound-diverges? ( base-case-info recursive-info -- t )
    [ interval>> to>> first ] bi@ < ;

! To check for divergence, the value-info union from the base-case branches must
! be compared to each incoming phi edge from a recursive call site.  Any of
! those can cause divergence.

: merge-base-case-infos ( phi-infos flags -- site-infos base-info )
    [ V{ } clone null-info ] 2dip
    [ [ clone value-info-union ] [ pick push ] if ] 2each ;

! Check if a call-site info phi edge causes divergence
: diverge-info ( base-case-info site-info -- info )
    dupd
    [ lower-bound-diverges? [ [ to>> { -1/0. t } swap <interval> ] change-interval ] when ]
    [ upper-bound-diverges? [ [ from>> { 1/0. t } <interval> ] change-interval ] when ] 2bi ;

! Check each call-site info phi edge whether it causes divergence
: diverge-phi-infos ( phi-infos flags -- infos )
    [ flip ] dip '[ _ merge-base-case-infos [ diverge-info ] reduce ] map ;

: infer-divergence ( #phi call-site -- )
    over
    [ phi-info-d>> ] [ remaining-branches>> ] [ out-d>> ] tri*
    [ diverge-phi-infos ] dip set-value-infos ;

: check-phi-divergence ( #phi -- )
    propagate-recursive? get
    [
        check-call-sites get ?last [ 2dup phi>> phi=
        [ infer-divergence ]
        [ 2drop ] if ] [ drop ] if*
    ] [ drop ] if
    ;
