USING: accessors compiler.tree.propagation.info
compiler.tree.propagation.mutually-recursive.interface
compiler.tree.propagation.mutually-recursive.pruning kernel locals math
math.intervals namespaces sequences ;

IN: compiler.tree.propagation.mutually-recursive

! In contrast to inline-recursive combinators, this pass deals with "regular"
! recursive calls for output value info propagation for single and mutual recursion.

! * Divergent output infos

! Divergence at phi nodes from recursive call sites

! Return t if the info interval from the recursive call site has a lower lower bound.
: lower-bound-diverges? ( rec-int return-int -- t )
    [ from>> first ] bi@ > ;

: upper-bound-diverges? ( rec-int return-int -- t )
    [ to>> first ] bi@ < ;

! Check if a call-site info phi edge causes divergence at a return site
: diverge-interval-absolute-bounds ( rec-int return-int -- int )
    tuck
    [ lower-bound-diverges? [ drop { -1/0. t } ] [ from>> ] if ]
    [ upper-bound-diverges? [ drop { 1/0. t } ] [ to>> ] if ] 3bi
    <interval>
    ;

! Version 1: Check any diverging paths.  Seems to be too conservative
! :: diverge-info-intervals ( rec-ints return-int -- return-int' )
!     rec-ints [ return-int [ interval-length ] bi@ < ] filter
!     return-int [ swap diverge-interval-absolute-bounds ] reduce ;

! Version 2: Look for any converging paths (assumes termination)
:: diverge-info-intervals ( rec-ints return-int -- return-int' )
    rec-ints [ interval-length ] map supremum
    return-int interval-length >=
    [ return-int ]
    [ rec-ints return-int [ swap diverge-interval-absolute-bounds ] reduce ]
    if ;

: diverge-info ( rec-infos return-info -- return-info' )
    clone tuck [ [ interval>> ] map ] [ interval>> ] bi*
    diverge-info-intervals
    >>interval ;

! TODO: change order of rec int and return int everywhere

! To check for divergence, the value-info union from the base-case branches must
! be compared to each incoming phi edge from a recursive call site.  Any of
! those can cause divergence.

: diverge-recursive-infos ( values -- )
   propagate-recursive? get [
        [ dup [ value-info ] [ get-rec-return-infos ] bi
          [ swap diverge-info swap set-value-info ]
          [ 2drop ] if*
        ] each
    ] [ drop ] if ;
