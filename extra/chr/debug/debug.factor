USING: assocs chr.refined kernel namespaces prettyprint ;

IN: chr.debug


: chr. ( -- )
    get-chr-state . ;

! * Debug
SYMBOL: saved-state
: save-chr ( -- )
    get-chr-state saved-state set ;

: load-chr ( -- )
    saved-state get [ swap set ] assoc-each ;
