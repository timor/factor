USING: accessors arrays chr.factor chr.parser combinators.short-circuit
combinators.smart hash-sets kernel sequences terms types.util ;

IN: chr.factor.util

! ** Stacks

: known-compatible-stacks? ( l1 l2 -- ? )
    { [ [ llength* ] same? ]
        [ [ lastcdr ] same? ] } 2&& ;

! ** Effect Type Isomorphism
GENERIC: expand-xor ( xor -- seq )
M: Xor expand-xor [ type1>> ] [ type2>> ] bi
    [ expand-xor ] bi@ append ;
M: object expand-xor 1array ;

GENERIC: effect>nterm ( effect -- term )
M: Xor effect>nterm
    expand-xor
    [ effect>nterm ] map >hash-set ;

M: object effect>nterm ;

M: Instance effect>nterm
    clone [ effect>nterm ] change-type ;

M: Effect effect>nterm
    {
        [ in>> ]
        [ out>> ]
        [ preds>>
          [ effect>nterm ] map >hash-set
        ]
        [ parms>> >hash-set ]
    } cleave>array ;

! The tag is unimportant for comparison
M: Iterated effect>nterm
    clone [ drop __ ] change-tag ;

: same-effect? ( e1 e2 -- ? )
    [ effect>nterm ] bi@ isomorphic? ;

! ** Recursion
: has-recursive-call? ( tag Effect -- ? )
    preds>> [ dup CallRecursive? [ tag>> = ] [ 2drop f ] if ] with any? ;
: filter-recursive-call ( tag Effect -- Effect )
    clone
    [ [ dup CallRecursive? [ tag>> = ] [ 2drop f ] if ] with reject ] with change-preds ;
GENERIC#: recursive-branches? 1 ( type word/quot -- ? )
M: Effect recursive-branches? swap has-recursive-call? ;
M: Xor recursive-branches? [ [ type1>> ] [ type2>> ] bi ] dip '[ _ recursive-branches? ] either? ;
GENERIC#: terminating-branches 1 ( type word/quot -- branches )
M: Effect terminating-branches over has-recursive-call? [ drop f ] [ 1array ] if ;
M: Xor terminating-branches [ [ type1>> ] [ type2>> ] bi ] dip '[ _ terminating-branches ] bi@ append sift ;
GENERIC#: recursive-branches 1 ( type word/quot -- branches )
M: Effect recursive-branches over has-recursive-call? [ 1array ] [ drop f ] if ;
M: Xor recursive-branches [ [ type1>> ] [ type2>> ] bi ] dip '[ _ recursive-branches ] bi@ append sift ;
