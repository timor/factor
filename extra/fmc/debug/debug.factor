USING: fmc io kernel prettyprint tools.annotations ;

IN: fmc.debug

: beta-state. ( stack: fmc-seq term: fmc-term -- stack term )
    "=========beta-state" print
    2dup swap "Stack: " write ... "Term: " write ...
    ;

: febug ( -- )
    \ (beta) [ [ beta-state. ] prepose ] annotate ;
