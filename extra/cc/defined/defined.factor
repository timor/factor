USING: accessors cc cc.reduction io.streams.string kernel match multiline parser
prettyprint prettyprint.backend prettyprint.custom prettyprint.sections
sequences words words.constant ;
IN: cc.defined


: define-ccn ( word cc-term -- )
    [ define-constant ]
    [ reduce-ccn register-normal-form ] 2bi ;

! Allow recursive definitions!
SYNTAX: CCN:
    scan-new-word
    [ t "ccn-def" set-word-prop ] keep
    ";" parse-multiline-string parse-ccn define-ccn ;

GENERIC: pprint-ccn* ( term -- str )
: enclose ( str -- str )
    "(" ")" surround ;
M: var pprint-ccn*
    name>> ;
PREDICATE: var-match-var < var name>> match-var? ;
M: var-match-var pprint-ccn*
    name>> [ pprint ] with-string-writer "<" ">" surround ;
SYNTAX: ⟼ -> suffix! ;
M: mapping pprint-ccn*
    [ var>> pprint-ccn* ]
    [ term>> pprint-ccn* ] bi
    " ⟼ " glue ;
M: ref pprint-ccn*
    word>> name>> ;
M: ext pprint-ccn*
    [ prev>> pprint-ccn* ]
    [ mapping>> pprint-ccn* ] bi
    " :: " glue enclose ;
M: abs pprint-ccn*
    [ subst>> pprint-ccn* "[" "]" surround ]
    [ var>> pprint-ccn* append ]
    [ term>> pprint-ccn* ] tri
    "." glue enclose ;
M: app pprint-ccn*
    [ left>> pprint-ccn* ]
    [ right>> pprint-ccn* ] bi
    " " glue enclose ;
M: tapp pprint-ccn*
    [ left>> pprint-ccn* ]
    [ right>> pprint-ccn* ] bi
    "@" glue enclose ;
M: I pprint-ccn* name>> ;

M: match-var pprint-ccn*
    [ pprint ] with-string-writer ;

M: cc-term pprint*
    \ CCN{ pprint-word
    pprint-ccn* text
    \ } pprint-word ;

M: ref pprint*
    M\ cc-term pprint* execute ;
