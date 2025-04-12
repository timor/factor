USING: continuations kernel namespaces persistent.disjoint-sets sequences
variables ;

IN: terms.context

! Disjoint set of variable equivalence sets
! terms.context vocabulary or some such
! TODO: find better name!
<< TYPED-GLOBAL: equivs maybe{ persistent-union-find } >>
! Option for optimization if equiv? is inlined:
! << TYPED-GLOBAL: equivs persistent-union-find >>

<PRIVATE

! NOTE: equivs-stack itself is _not_ a global!
SYMBOL: equivs-stack

PRIVATE>

! : save-equivs ( quot -- )
: with-equiv-scope ( quot -- )
    equivs-stack [ equivs suffix ] change
    [ T{ persistent-union-find } or ] change: equivs
    [ equivs-stack get unclip-last-slice set: equivs
      equivs-stack set
    ] finally ; inline

: on-equivs ( quot: ( ..a equivs -- ..b equivs ) -- )
    equivs swap call set: equivs ; inline

! TODO: this always checks for existing atoms.  If that is a bottlenck, it could
! be tackled by forcing an equiv scope whenever variables are instantiated
! somehow, and directly adding them then?
: equate-vars ( a b -- )
    [| a b puf | puf a added-atom b added-atom a b equated ] change: equivs ;

: vars-equiv? ( a b -- ? )
    equivs equiv? ;

: add-vars ( vars -- )
    [ swap [ added-atom ] each ] change: equivs ;
