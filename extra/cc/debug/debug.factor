USING: cc.reduction kernel memoize namespaces sequences tools.annotations ;

IN: cc.debug

: debug-rewrite ( -- )
    \ rewrite-ccn [ [ reset-word-timing ] prepose [ word-timing. ] compose ] annotate ;

: reset-memos ( -- )
    { rewrite-ccn-cached rewrite-ccn-step-cached } [ reset-memoized ] each ;

: rebug ( -- )
    reset-memos
    { rewrite-ccn-step rewrite-ccn-step-cached rewrite-ccn-uncached rewrite-ccn-cached } [ add-timing ] each
    debug-rewrite ;

: re ( term -- term )
    reset-memos rewrite-ccn ;

: nre ( term -- term )
    normalize? [ re ] with-variable-on ;
