USING: assocs cc cc.reduction kernel multiline namespaces parser words
words.constant ;
IN: cc.defined


: define-ccn ( word ccn-term -- )
    [ define-constant ]
    [ rewrite-ccn normal-cache get set-at ] 2bi ;

! Allow recursive definitions!
SYNTAX: CCN:
    scan-new-word
    [ t "ccn-def" set-word-prop ] keep
    ";" parse-multiline-string parse-ccn define-ccn ;
