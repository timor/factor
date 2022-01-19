USING: accessors arrays assocs kernel lists match math parser prettyprint.custom
sequences types.util vectors words ;

IN: patterns.terms

FROM: syntax => _ ;
! Factorization protocol
MIXIN: app-term
GENERIC: left/right ( app -- left right )
GENERIC: head-term ( term -- term )
GENERIC: new-app-term ( left right exemplar -- app-term )

INSTANCE: list app-term
M: list left/right uncons ;
M: list head-term car ;
M: cons-state new-app-term drop
    cons ;

! Head sequence
UNION: array-like array slice ;
PREDICATE: app-seq < array-like length 1 > ;
PREDICATE: head-seq < array-like length 1 = ;
INSTANCE: app-seq app-term
GENERIC: maybe-unseq ( seq -- term )
M: head-seq maybe-unseq first ;
M: object maybe-unseq ;
M: vector maybe-unseq >array maybe-unseq ;
M: app-seq head-term first ;
M: app-seq left/right
    unclip-last-slice
    [ maybe-unseq ] dip ;
GENERIC: maybe-seq ( obj -- seq )

M: array-like maybe-seq ;
M: object maybe-seq 1array ;
M: app-seq new-app-term
    '[ maybe-seq _ like ] dip suffix ;

SINGLETON: nomatch

: <psym> ( name -- pattern-symbol )
    uvar <uninterned-word> [ t "pattern-symbol" set-word-prop ] keep ;

PREDICATE: pattern-symbol < word "pattern-symbol" word-prop? ;
INSTANCE: pattern-symbol match-var


TUPLE: pcase pattern body ;
C: <pcase> pcase

SYMBOL: ->
SYNTAX: P{ -> parse-until \ } parse-until [ maybe-unseq ] bi@ <pcase> suffix! ;
M: pcase pprint* pprint-object ;
M: pcase pprint-delims drop \ P{ \ } ;
M: pcase >pprint-sequence
    [ pattern>> ] [ body>> ] bi
    [ maybe-seq ] bi@ { -> } glue ;

! TUPLE: special-case pcase default ;
! C: <special-case> special-case
! Cond structure
! : <extension> ( cases default -- case )
!     [ <reversed> ] dip
!     [ first2 <pcase> swap <special-case> ] reduce ;

:: <special-case> ( p s r -- term )
    "x" <psym> :> x
    "y" <psym> :> y
    "z" <psym> :> z
    x
    { nomatch y } y <pcase>
    p z { nomatch s } <pcase> <pcase> x { r x } 3array
    2array <pcase> ;

: <extension> ( cases default -- case )
    [ <reversed> ] dip
    [ first2 rot <special-case> ] reduce ;

SINGLETONS: undefined none ;
UNION: match-result assoc undefined none ;

PREDICATE: constructor < word match-var? not ;

PREDICATE: compound < app-term head-term constructor? ;
UNION: data constructor compound ;
UNION: matchable data pcase ;
