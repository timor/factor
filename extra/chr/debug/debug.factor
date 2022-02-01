USING: accessors arrays assocs chr chr.state classes combinators formatting io
kernel namespaces prettyprint sequences ;

IN: chr.debug

: id-cons. ( seq -- )
    [ [ id>> ] [ cons>> cons>> ] bi 2array ] map . ;

: classify-consts ( -- assoc )
    exec-stack get [ class-of ] collect-by ;

: exec-stack. ( -- )
    classify-consts
    {
        [ active-cons of [ "Activated: " write [ cons>> ] map id-cons. ] unless-empty ]
        [ id-cons of [ "Identified: " write id-cons. ] unless-empty ]
        [ chr-cons of [ "New-Chr: " write [ cons>> ] map . ] unless-empty ]
        [ builtin-cons of [ "New-Builtin: " write [ cons>> ] map . ] unless-empty ]
    } cleave ;

: chr-consts. ( -- )
    "Store: " write store get id-cons. ;

: builtins. ( -- )
    "Builtins: " write builtins get . ;

: chr. ( -- )
    current-index get "N: %d\n" printf
    exec-stack.
    chr-consts.
    builtins. ;

! * Debug
SYMBOL: saved-state
: save-chr ( -- )
    get-chr-state saved-state set ;

: load-chr ( -- )
    saved-state get [ swap set ] assoc-each ;


TUPLE: chr-log-entry { transition read-only } { rule-id read-only } { delta read-only } ;
C: <chr-log-entry> chr-log-entry

SYMBOL: debug-chr
: debug-chr? ( -- ? )
    debug-chr get ;

: log-chr ( transition rule-id delta -- )
    debug-chr? [ <chr-log-entry> . ] [ 3drop ] if ;
