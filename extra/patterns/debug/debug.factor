USING: formatting io kernel namespaces patterns.reduction patterns.terms
tools.annotations ;

IN: patterns.debug

: <mid> ( -- n )
    \ <mid> counter ;

: rule-start. ( pattern term id -- pattern term )
    2over swap ">>(%d)Apply Term %u \n on Pattern: %u" printf nl ;

: rule-match. ( result id -- result )
    "<<(%d)" printf
    dup nomatch? [ "Nomatch" print ]
    [ dup "Success: %u" printf nl ] if ;

:: wrap-do-match ( def -- quot )
    [ <mid> [ rule-start. def call( pattern term -- result ) ] keep rule-match. ] ;

: pebug ( -- )
    \ do-match-rule
    [ wrap-do-match ] annotate ;
