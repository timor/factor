USING: continuations namespaces persistent.disjoint-sets sequences variables ;

IN: terms.context

! Disjoint set of variable equivalence sets
! terms.context vocabulary or some such
! TODO: find better name!
<< TYPED-GLOBAL: equivs persistent-union-find >>

<PRIVATE

! NOTE: equivs-stack itself is _not_ a global!
SYMBOL: equivs-stack

PRIVATE>

! : save-equivs ( quot -- )
: with-equiv-scope ( quot -- )
    equivs-stack [ equivs suffix ] change
    [ equivs-stack get unclip-last-slice set: equivs
      equivs-stack set
    ] finally ; inline

! : with-equivs ( quot: ( equivs ..a -- equivs ..b ) -- )
!     equivs swap call set: equivs

: equate-vars ( a b -- )
    [ break equated ] change: equivs ;
