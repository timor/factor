USING: accessors compiler.tree.propagation.info
compiler.tree.propagation.mutually-recursive.interface
compiler.tree.propagation.mutually-recursive.pruning kernel locals math
math.intervals namespaces sequences ;

IN: compiler.tree.propagation.mutually-recursive

! In contrast to inline-recursive combinators, this pass deals with "regular"
! recursive calls for output value info propagation for single and mutual recursion.

! * Divergent output infos

! Divergence at phi nodes from recursive call sites

! Return t if the info from the recursive call site has a lower lower bound.
: lower-bound-diverges? ( rec-info return-info -- t )
    [ interval>> from>> first ] bi@ > ;

: upper-bound-diverges? ( rec-info return-info -- t )
    [ interval>> to>> first ] bi@ < ;

! To check for divergence, the value-info union from the base-case branches must
! be compared to each incoming phi edge from a recursive call site.  Any of
! those can cause divergence.

! Check if a call-site info phi edge causes divergence at a return site
! modifies rec-info!
: diverge-info ( rec-info return-info -- info )
    dupd
    [ lower-bound-diverges? [ [ to>> { -1/0. t } swap <interval> ] change-interval ] when ]
    [ upper-bound-diverges? [ [ from>> { 1/0. t } <interval> ] change-interval ] when ] 2bi ;

! For the values in question,
: diverge-recursive-infos ( values -- )
   propagate-recursive? get [
        [ dup [ value-info ] [ get-rec-return-info ] bi
          [ swap diverge-info swap set-value-info ]
          [ 2drop ] if*
        ] each
    ] [ drop ] if ;

    ! dup pop-rec-return-infos/f
    ! [ [| val rec-info | val value-info rec-info diverge-info  ] 2each ]
    ! [ drop ] if* ;
