USING: accessors continuations kernel match math multiline parser peg peg.ebnf
sequences strings typed variants vocabs.parser words words.constant ;

IN: cc

FROM: variants => match ;

! * Closure calculus
! ** CCN
VARIANT: ccn-term
    I
    var: { name }
    app: { left right }
    mapping: { var term }
    ext: { prev mapping }
    abs: { subst var term }
    ;

TUPLE: tapp < app ;
C: <tapp> tapp

TUPLE: ref word ;
C: <ref> ref

VARIANT: ccn-token
    tag
    impl-app
    open
    close
    ->
    dcol
    abbrev: { name }
    lbracket
    rbracket
    dot
    ;

SINGLETONS: +bind+ ;
TUPLE: bind-op subst var ;
C: <bind-op> bind-op
TUPLE: lam var body ;
C: <lam> lam

UNION: operator tag impl-app -> dcol dot +bind+ ;
UNION: operand I var match-var ref ;

GENERIC: ccn-def ( word -- term/f )
M: f ccn-def ;
M: word ccn-def "ccn-def" word-prop ;
M: constant ccn-def "constant" word-prop ;
: <var-or-ref> ( name -- term )
    dup search dup ccn-def [ <ref> nip ]
    [ drop <var> ] if ;

EBNF: tokenize-ccn
[=[
     Letter            = [a-zA-Z]
     Digit             = [0-9]
     Digits            = Digit+
     LineTerminator    = [\r\n\u002028\u002029]
     WhiteSpace        = [ \t\v\f\xa0\u00feff\u001680\u002000\u002001\u002002\u002003\u002004\u002005\u002006\u002007\u002008\u002009\u00200a\u00202f\u00205f\u003000]
     Space             = WhiteSpace | LineTerminator
     Spaces            = Space* => [[ ignore ]]
     NameFirst         = Letter | "_" => [[ CHAR: _ ]]
     NameRest          = NameFirst | Digit
     Keyword           = ("I" => [[ drop I ]]) !(NameRest)
     iName             = NameFirst NameRest* => [[ first2 swap prefix >string ]]
     SVarName          = "?" NameRest* => [[ first2 >string swap prepend ]]
     Name              = !(Keyword) iName
     Id                = Name => [[ <var-or-ref> ]]
     LB                = "[" => [[ drop lbracket ]]
     RB                = "]" => [[ drop rbracket ]]
     Open              = "(" => [[ drop open ]]
     Close             = ")" => [[ drop close ]]
     DCol              = "::" => [[ drop dcol ]]
     Tag               = "@" => [[ drop tag ]]
     Arrow             = ("->" | "⟼") => [[ drop -> ]]
     Dot               = "." => [[ drop dot ]]
     Abbrev            = "," Spaces Tok => [[ second <abbrev> ]]
     SVar              = "<" Spaces SVarName Spaces ">" => [[ second parse-datum <var> ]]
     PVar              = SVarName => [[ parse-datum ]]
     Special           = SVar | Abbrev | PVar | Open | Close | DCol | Tag | Arrow | Dot | LB | RB
     Tok               = Spaces (Id | Keyword | Special)
     Toks              = Tok* Spaces
 ]=]


UNION: left-bound open operator lbracket rbracket abbrev ;
GENERIC: add-app-op ( last this -- ? )
M: operand add-app-op drop
    left-bound? not ;
M: open add-app-op drop
    left-bound? not ;
M: lbracket add-app-op drop
    left-bound? not ;
M: object add-app-op 2drop f ;

: normalize-ccn-tokens ( tokens -- tokens )
    1 cut-slice
    [
        2dup [ last ] dip
        add-app-op [ [ impl-app suffix ] dip ] when
        suffix
    ] each open prefix close suffix ;

GENERIC: push-postfix* ( pf obj -- pf )

M: operand push-postfix*
    suffix ;
M: ccn-term push-postfix*
    suffix ;
M: impl-app push-postfix* drop
    [ <app> ] with-datastack ;
M: tag push-postfix* drop
    [ <tapp> ] with-datastack ;
TYPED: make-abs ( :bind-op body -- :abs )
    [ [ subst>> ] [ var>> ] bi ] dip <abs> ;
M: +bind+ push-postfix* drop
    [ <bind-op> ] with-datastack ;
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
    { f open dcol -> impl-app dot +bind+ tag  } index ;

GENERIC#: precedence>= 1 ( op1 op2 -- ? )

M: object precedence>=
    [ precedence ] bi@ >= ;
M: dot precedence>=
    2dup = [ 2drop f ] [ call-next-method ] if ;

: compare-op> ( stack obj -- ? )
    [ ?last ] dip precedence>= ;

: exchange ( pf stack -- pf stack )
    unclip-last-slice push-postfix ;

: unwind ( pf stack -- pf stack )
    unclip-last-slice dup open?
    [ drop ] [ push-postfix unwind ] if ;

GENERIC: handle-operator ( pf stack oper -- pf stack )

! When encountering binder
M: operator handle-operator
    [ 2dup compare-op> ] [ [ exchange ] dip ] while
    push-operator ;

: parse-ccn-token ( postfix stack token -- postfix stack )
    {
        { abbrev [ [ dcol handle-operator ] dip
                   [ push-postfix -> handle-operator ]
                   [ push-postfix ] bi
                 ] }
        { open [ open push-operator ] }
        { lbracket [ open push-operator ] }
        { close [ unwind ] }
        { rbracket [ unwind +bind+ handle-operator ] }
        [
            dup operator?
            [ handle-operator ]
            [ push-postfix ] if
        ]
    } match ;

: parse-ccn ( str -- term )
    tokenize-ccn normalize-ccn-tokens [ f f ] dip [ parse-ccn-token ] each
    drop last ;

