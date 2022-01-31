USING: assocs kernel namespaces ;

IN: chr.state

TUPLE: chr-state stack store builtins trace n vars ;

SYMBOLS: program exec-stack store builtins match-trace current-index ;

: reset-chr-state ( -- )
    exec-stack off
    store off
    builtins off
    match-trace off
    0 current-index set ;

: with-new-chr-state ( quot -- )
    [ reset-chr-state ] prepose with-scope ; inline

: get-chr-state ( -- assoc )
    { program exec-stack store builtins match-trace current-index }
    [ dup get ] H{ } map>assoc ;
