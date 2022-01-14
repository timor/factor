USING: accessors continuations kernel math multiline peg peg.ebnf sequences
strings typed variants ;

IN: cc

FROM: variants => match ;

! * Closure calculus
! ** CCN
VARIANT: ccn-term
    I
    var: { name }
    app: { left right }
    ! tapp: { left right }
    mapping: { var term }
    ext: { prev mapping }
    abs: { subst var term }
    ;

TUPLE: tapp < app ;
C: <tapp> tapp

! Name              = !(Keyword) iName => [[ ast-name boa ]]
VARIANT: ccn-token
    tag
    impl-app
    open
    close
    ->
    dcol
    id: { name }
    lbracket
    rbracket
    dot
    ;

SINGLETON: +in+
UNION: operator tag impl-app -> dcol dot +in+ ;
UNION: operand I var id ;


EBNF: tokenize-ccn
[=[
     Letter            = [a-zA-Z]
     Digit             = [0-9]
     Digits            = Digit+
     LineTerminator    = [\r\n\u002028\u002029]
     WhiteSpace        = [ \t\v\f\xa0\u00feff\u001680\u002000\u002001\u002002\u002003\u002004\u002005\u002006\u002007\u002008\u002009\u00200a\u00202f\u00205f\u003000]
     Space             = WhiteSpace | LineTerminator
     Spaces            = Space* => [[ ignore ]]
     NameFirst         = Letter
     NameRest          = Letter | Digit
     Keyword           = ("I" => [[ drop I ]]) !(NameRest)
     iName             = NameFirst NameRest* => [[ first2 swap prefix >string ]]
     Name              = !(Keyword) iName => [[ <id> ]]
     LB                = "[" => [[ drop lbracket ]]
     RB                = "]" => [[ drop rbracket ]]
     Open              = "(" => [[ drop open ]]
     Close             = ")" => [[ drop close ]]
     DCol              = "::" => [[ drop dcol ]]
     Tag               = "@" => [[ drop tag ]]
     Arrow             = "->" => [[ drop -> ]]
     Dot               = "." => [[ drop dot ]]
     Special           = Open | Close | DCol | Tag | Arrow | Dot | LB | RB
     Tok               = Spaces (Name | Keyword | Special)
     Toks              = Tok* Spaces
 ]=]


TUPLE: bind-op subst var ;
C: <bind-op> bind-op

UNION: left-bound open operator lbracket rbracket ;
GENERIC: add-app-op ( last this -- ? )
M: operand add-app-op drop
    left-bound? not ;
M: open add-app-op drop
    left-bound? not ;
M: lbracket add-app-op drop
    left-bound? not ;
M: object add-app-op 2drop f ;

: normalize-ccn ( tokens -- tokens )
    1 cut-slice
    [
        2dup [ last ] dip
        add-app-op [ [ impl-app suffix ] dip ] when
        suffix
    ] each open prefix close suffix ;

GENERIC: push-postfix* ( pf obj -- pf )

M: operand push-postfix*
    suffix ;
M: impl-app push-postfix* drop
    [ <app> ] with-datastack ;
M: tag push-postfix* drop
    [ <tapp> ] with-datastack ;
M: +in+ push-postfix* drop
    [ <bind-op> ] with-datastack ;
TYPED: make-abs ( :bind-op body -- :abs )
    [ [ subst>> ] [ var>> ] bi ] dip <abs> ;
M: dot push-postfix* drop
    [ make-abs ] with-datastack ;
M: -> push-postfix* drop
    [ <mapping> ] with-datastack ;
M: dcol push-postfix* drop
    [ <ext> ] with-datastack ;

: push-postfix ( pf stack obj -- pf stack )
    swap [ push-postfix* ] dip ;

: push-operator ( pf stack obj -- pf stack )
    suffix ;

MEMO: precedence ( operator -- n )
    { f open dcol -> impl-app dot +in+ tag } index ;

: compare-op> ( stack obj -- ? )
    [ ?last ] dip [ precedence ] bi@ >= ;

: exchange ( pf stack -- pf stack )
    unclip-last-slice push-postfix ;

: unwind ( pf stack -- pf stack )
    unclip-last-slice dup open?
    [ drop ] [ push-postfix unwind ] if ;

: handle-operator ( pf stack oper -- pf stack )
    [ 2dup compare-op> ] [ [ exchange ] dip ] while
    push-operator ;

: parse-ccn-token ( postfix stack token -- postfix stack )
    {
        { id [ <var> push-postfix ] }
        { I [ I push-postfix ] }
        { open [ open push-operator ] }
        { lbracket [ open push-operator ] }
        { close [ unwind ] }
        { rbracket [ unwind +in+ handle-operator ] }
        [ handle-operator ]
    } match ;

: parse-ccn ( str -- term )
    tokenize-ccn normalize-ccn [ f f ] dip [ parse-ccn-token ] each
    drop last ;

SYNTAX: CCN{ "}" parse-multiline-string parse-ccn suffix! ;

GENERIC: pprint-ccn* ( term -- str )
: enclose ( str -- str )
    "(" ")" surround ;
M: var pprint-ccn*
    name>> ;
M: mapping pprint-ccn*
    [ var>> pprint-ccn* ]
    [ term>> pprint-ccn* ] bi
    "->" glue ;
M: ext pprint-ccn*
    [ prev>> pprint-ccn* ]
    [ mapping>> pprint-ccn* ] bi
    "::" glue ;
M: abs pprint-ccn*
    [ subst>> pprint-ccn* "[" "]" surround ]
    [ var>> pprint-ccn* append ]
    [ term>> pprint-ccn* ] tri
    "." glue ;
M: app pprint-ccn*
    [ left>> pprint-ccn* ]
    [ right>> pprint-ccn* ] bi
    " " glue enclose ;
M: tapp pprint-ccn*
    [ left>> pprint-ccn* ]
    [ right>> pprint-ccn* ] bi
    "@" glue enclose ;
M: I pprint-ccn* name>> ;

M: ccn-term pprint*
    \ CCN{ pprint-word
    pprint-ccn* text
    \ } pprint-word ;
