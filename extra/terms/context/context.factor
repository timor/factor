USING: accessors assocs continuations disjoint-sets kernel namespaces
persistent.assocs persistent.disjoint-sets sequences terms.relations variables ;

IN: terms.context

! Disjoint set of variable equivalence sets

<< TYPED-GLOBAL: equivs maybe{ term-relation } >>
! Option for optimization if equiv? is inlined:
! << TYPED-GLOBAL: equivs term-relation >>

<PRIVATE

! NOTE: equivs-stack itself is _not_ a global!
SYMBOL: equivs-stack

! : save-equivs ( quot -- )
! NOTE: that clone call is due to being too lazy to completely reconstruct the
! term relation in set-rep-schema!
: push-equivs ( -- )
    equivs-stack [ equivs suffix ] change
    [ [ clone ] [ term-relation new ] if* ] change: equivs ;

: pop-equivs ( -- )
    equivs-stack get unclip-last-slice set: equivs
    equivs-stack set ;

PRIVATE>

: with-match ( quot -- )
    push-equivs
    [ pop-equivs
    ] finally ; inline

: on-equivs ( quot: ( ..a equivs -- ..b equivs ) -- )
    equivs swap call set: equivs ; inline

: add-var ( var -- )
    [ swap added-atom ] change: equivs ;

: add-vars ( vars -- )
    [ swap [ added-atom ] each ] change: equivs ;

! TODO: this always checks for existing atoms.  If that is a bottlenck, it could
! be tackled by forcing an equiv scope whenever variables are instantiated
! somehow, and directly adding them then?
! NOTE: this is done at the underlying data structure for now
: equate-vars ( a b -- )
    ! [| a b puf | puf a added-atom b added-atom a b equated ] change: equivs ;
    [| a b puf | puf a b equated ] change: equivs ;

! TODO: same overhead here
: vars-equiv? ( a b -- ? )
    2dup [ add-var ] bi@
    equivs equiv? ;

: var-rep ( var -- representative )
    equivs representative ;

: get-schema ( thing -- var/term )
    dup equivs [ representative ] [ schema>> ] bi ?at
    spin ? ;

! NOTE: not rebuilding the whole thing here.  Subject to scoping!
: set-rep-schema ( term rep -- )
    equivs [ new-at ] change-schema drop ;
