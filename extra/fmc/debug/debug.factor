USING: combinators fmc io kernel prettyprint tools.annotations ;

IN: fmc.debug

: beta-state. ( stack: fmc-seq term: fmc-term -- stack term )
    "=========beta-state" print
    2dup swap "Stack: " write ... "Term: " write ...
    ;

: fmc-subst. ( m: fmc-term v: varname n: fmc m/xn: fmc -- )
    "============subst" print
    { [ " Subst: " write ... ]
      [ " for: " write ... ]
      [ " in: " write ... ]
      [ "=> " write ... ]
    } spread ;

: beta-subst.-1 ( m: fmc-term v: varname n: fmc -- )
    "=========beta-subst" print
    [ " Subst: " write ... ]
    [ " for: " write ... ]
    [ " in: " write ... ]
    tri* ;

: beta-subst.-2 ( m/xn: fmc -- )
    "==> " write ...  ;

: febug ( -- )
    \ (beta) [ [ beta-state. ] prepose ] annotate
    ! \ beta-subst watch
    \ (subst-fmc) [ '[ _ 3keep reach fmc-subst. ] ] annotate
    \ beta-subst [ [ 3dup beta-subst.-1 ] prepose [ dup beta-subst.-2 ] compose ] annotate
    ;
