USING: accessors hashtables kernel match patterns.reduction patterns.terms words
;

IN: patterns.static

FROM: patterns.terms => undefined ;

! * Static pattern calculus

PREDICATE: constructor < word match-var? not ;

PREDICATE: compound < app-term head-term constructor? ;

UNION: data constructor compound host-data ;
UNION: matchable data pcase ;

GENERIC: matching ( term pattern -- result )
M: match-var matching
    associate ;
M: constructor matching
    2dup = [ 2drop f ]
    [ call-next-method ] if ;
: destructure-match ( compound-term app-term -- result )
    [ left/right ] bi@ swapd
    [ matching ] 2bi@ match-disjoint-union ;
M: app-term matching
    over compound? [ destructure-match ]
    [ call-next-method ] if ;
M: object matching
    drop matchable? none undefined ? ;

M: pcase do-match-rule ( pcase term -- result: match-app )
    swap [ pattern>> ] [ body>> ] bi [ matching ] dip match-rule ;

