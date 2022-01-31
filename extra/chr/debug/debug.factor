USING: assocs chr.state kernel namespaces prettyprint ;

IN: chr.debug


: chr. ( -- )
    get-chr-state . ;

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
