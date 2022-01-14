USING: accessors arrays combinators compiler.tree.debugger continuations kernel
lists match math multiline namespaces peg peg.ebnf sequences strings typed
variants vectors ;

IN: cc

FROM: variants => match ;

! * Closure calculus
! ** CCN
VARIANT: cc-term
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
    lam
    id: { name }
    lbracket
    rbracket
    dot
    ;

SINGLETON: +in+
UNION: operator tag impl-app -> dcol dot +in+ ;
UNION: operand I var id lam ;


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
     Keyword           = ("I" => [[ drop I ]] | "lam" => [[ drop lam ]] ) !(NameRest)
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

PREDICATE: app-stack < sequence empty? not ;
PREDICATE: tapp-stack < app-stack last tag? ;
! PREDICATE: start-stack < app-stack last f = ;

GENERIC#: build-app 1 ( accum obj -- accum )
M: app-stack build-app
    [ unclip-last-slice ] dip swap [ swap <app> ] when* suffix ;
M: tapp-stack build-app
    [ unclip-last-slice drop
      unclip-last-slice ] dip swap
    [ swap <tapp> ] when* suffix ;
M: f build-app nip 1array ;
! M: start-stack build-app
!     unclip-last-slice drop swap suffix ;

MATCH-VARS: ?a ?s ?t ?u ?x ;

! GENERIC: make-app ( accum obj -- accum )
! M: id make-app name>> <var> make-app ;
! M: object make-app
!     [ [ unswons ] dip
!       over
!       [ <app> ]
!       [ nip ] if swons
!     ] when* ;

! DEFER: make-ccn
! : cont ( obj -- term )
!     replace-patterns make-ccn ; inline

! : need-app? ( last next -- ? )
!     { [ dup operand? ] [ over  ] }

! Helpers for parsing lambda expressions
! TUPLE: start-abs lambda env ;
! C: <start-abs> start-abs
! TUPLE: mid-abs start var ;
! C: <mid-abs> mid-abs
! TUPLE: end-abs mid body ;
! C: <end-abs> end-abs

TUPLE: bind-op subst var ;
C: <bind-op> bind-op

UNION: left-bound open operator lbracket rbracket ;
! UNION: right-bound close operator rbracket ;
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
        { ! { [ dup lbracket? ] [ suffix open suffix ] }
          ! { [ dup rbracket? ] [ [ close suffix ] dip suffix ] }
          [ suffix ]
        } cond
    ] each open prefix close suffix ;

: make-app ( stack -- stack )
    unclip-last
    [ [ ] [ <app> ] map-reduce suffix ] unless-empty ;

GENERIC: push-postfix* ( pf obj -- pf )

M: operand push-postfix*
    suffix ;
M: impl-app push-postfix* drop
    [ <app> ] with-datastack ;
M: tag push-postfix* drop
    [ <tapp> ] with-datastack ;
! M: lbracket push-postfix* drop
!     [ <start-abs> ] with-datastack ;
! M: rbracket push-postfix* drop
!     [ <mid-abs> ] with-datastack ;
M: +in+ push-postfix* drop
    [ <bind-op> ] with-datastack ;
! TYPED: make-abs ( :mid-abs body -- :abs )
!     [ [ start>> env>> ] [ var>> ] bi ] dip <abs> ;
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
        ! { lam [ lam push-postfix ] }
        { open [ open push-operator ] }
        { lbracket [ open push-operator ] }
        { close [ unwind ] }
        { rbracket [ unwind +in+ handle-operator ] }
        [ handle-operator ]
    } match ;

! : parse-ccn-stack ( stack token -- stack )
!     {
!         { open [ open suffix ] }
!         { lbracket [ lbracket suffix ] }
!         {  }


!     } match


: parse-ccn ( str -- term )
    tokenize-ccn normalize-ccn [ f f ] dip [ parse-ccn-token ] each
    drop ;

! : add ( accum tokens obj -- accum tokens )
!     swap [ suffix ] dip ;

SYMBOL: tokens

: next ( -- obj/f )
    tokens get
    [ f ]
    [ unclip-slice [ tokens set ] dip ] if-empty ;

: unread ( obj -- )
    tokens [ swap prefix ] change ;

: add ( accum obj -- accum )
    [ suffix ] when* ;

: unadd ( accum -- accum obj )
    unclip-last ;

DEFER: parse-app
: (parse-term) ( next -- term )
    dup open? [ drop f parse-app ] when ; inline

: parse-term ( -- term )
    next dup
    [ (parse-term) ] when ;

: pair-app ( l r -- app/f )
    2dup and [ <app> ] [ or ] if ;

: end-app ( accum -- term )
    [ f ] [ [ ] [ pair-app ] map-reduce ] if-empty ;

: parse-var ( -- var )
    next dup id? [ "not-a-var" 2array throw ] unless
    name>> <var>
    next dot? [ "not-a-dot" throw ] unless
    ;

: parse-app ( accum -- term )
    next dup .
    [
        {
            { open [ end-app f parse-app [ pair-app ] when* 1array parse-app ] }
            { id [ <var> add parse-app ] }
            { I [ I add parse-app ] }
            { close [ end-app ] }
            { rbracket [ end-app ] }
            { tag [ unadd parse-term <tapp> add parse-app ] }
            { lbracket [ f parse-app parse-var parse-term <abs> add parse-app ] }
            { -> [ unadd parse-term <mapping> add parse-app ] }
            { dcol [ unadd parse-term <ext> add parse-app ] }
        } match
    ] [ "error" throw ] if* ;

! : parse-ccn ( str -- term )
!     tokenize-ccn close suffix tokens [ f parse-app ] with-variable ;

    ! { { [ dup open? ] [ drop make-app { } suffix ] }
    !   { [ dup close? ] [ drop make-app ] }
    !   { [ dup tag? ] }
    ! }
    ! l
    ! token open?
    ! stack token suffix block

    ! [ f ] [
    !     normalize-ccn
    !     V{ } clone :> postfix
    !     V{ } clone :> stack
    !     tokens [
    !         tokens ?first :> peek
    !         {
    !             { [ dup open? ] [ op-stack push ] }
    !             { [ dup operand? ] }
    !         } cond
    !     ] each
    ! ] if-empty


! SYMBOL: tag?
! :: make-ccn ( tokens -- term )
!     tokens {
!         { [ empty? ] [ f ] }
!         { [ length 1 = ] [ first ] }
!         [ unclip-slice :> ( rest fst ) {
!               fst open?
!               [ rest [ close? ] split-when :> ( inner rest )
!                 inner [ open? ] any
!               ]
!           } cond ]
!     } cond ;

! :: make-ccn ( list -- term )
!     list {
!         { L{ } [ f ] }
!         { L{ ?a } [ ?a ] }
!         !  { L{ ?a tag ?s . ?u }
!         !   [ ?a ?s <tapp> :> tt
!         !     L{ tt . ?u } cont ]
!         ! }
!         { L{ ?a tag open . ?u }
!           [ L{ L{ ?a tag } open . ?u } cont ]
!         }
!         { L{ open . ?u }
!           [ L{ L{ } open . ?u } cont ]
!         }
!         { L{ ?a open close . ?u }
!           [ ?a make-ccn :> tt
!             L{ ?a tt . ?u } cont ]
!         }
!         { L{ L{ } close . ?u }
!           [ ?u cont ]
!         }
!         { L{ L{ ?a . ?s } close . ?u }
!           [ L{ ?s close ?a . ?u } cont ]
!         }
!         { L{ ?a open open . ?u }
!           [ L{ L{ ?a . open } openL{ f . ?a } . ?u } cont ]
!         }
!         { L{ ?a close . ?u }
!           [ ?a uncons :> ( tt aa )
!             L{ tt aa . ?u } cont
!           ] }
!         { L{ f f . ?u }
!           [ ?u ] cont
!         }
!         { L{ f ?a . ?u }
!           [ L{ ?a . ?u } cont ]
!         }
!         { L{ ?a f . ?u }
!           [ L{ ?a . ?u } cont ]
!         }
!         { L{ ?a ?b . ?u }
!           [ ?a ?b <app> :> tt
!             L{ tt . ?u } cont ]
!         }
!         ! { L{ close . ?u }
!         !   [ unswons make-app ?u make-ccn ]
!         ! }
!         ! { L{ tag . ?u }
!         !   [  ]
!         ! }
!         ! { L{ ?s . ?u }
!         !   [ ?s make-app ?u make-ccn ]
!         ! }
!         [  ]
!     } match-cond ;

! : make-ccn ( tokens accum -- tokens term )
!     over empty?
!     [ first ]
!     [ [ unclip-slice ] dip swap
!       {
!           { id [ <var> build-app make-ccn ] }
!           { tag [ tag suffix make-ccn ] }
!           { I [ I build-app make-ccn ] }
!           { open [| rest acc |
!                   rest f make-ccn :> ( rest tt )
!                   rest acc tt build-app make-ccn
!                  ] }
!           { close [ dup length 1 > [ "invalid term" throw ] when first ] }
!           {  }
!       } match ] if ;

! <a a b> => <<a.a>.b>
! <a a <b c>> => <<a.a>.<b.c>>
! <a a <b>> => <<a.a>.b>
! <a a <b b> <c c>> => <<<a.a>.<b.b>>.<c.c>>
! <a a @ <b b> <c c>> => <<<a.a>@<b.b>>.<c.c>>
! <<<a>>>
! SINGLETON: tag
SYMBOL: accum
: app, ( expr -- )
    accum get pop
    [ dup tag?
      [ drop accum get pop swap <tapp> ]
      [ swap <app> ] if
    ] when*
    accum get push ;

: <accum> ( -- )
    f 1vector accum set ;

: ,open ( -- )
    f accum get push ;

: ,close ( -- )
    accum get pop
    [ ! accum get pop
      ! [ swap <app> accum get push ] when*
      app,
    ] when* ;

ERROR: ccn-parse-error ;
: ,tag ( -- )
    accum get last cc-term? not [ ccn-parse-error ]
    [ tag accum get push ] if ;


! EBNF: parse-ccn
! [=[
!      tokenizer = <foreign tokenize-ccn Tok>
!      Icomb = "I" => [[ drop I ]]
!      Name  = <foreign tokenize-ccn Name>
!      Spaces = <foreign tokenize-ccn Spaces>
!      var = Name => [[ <var> ]]
!      End = !(.) | &( ")" ) | &( "}" )

!      atom = Icomb
!      | var
!      |

!      open = "(" => [[ ,open ]]
!      close = ")" => [[ ,close ]]
!      tag = "@" => [[ ,tag ]]

!      leaf = atom => [[ dup app, ]]
!      | open Spaces term close

!      term = End
!      | leaf Spaces tag Spaces term
!      | leaf Spaces term
!  ]=]

! : ccn ( str -- ast term )
!     [ <accum> parse-ccn accum get ] with-scope ;

! term = primterm
! | term Spaces term End => [ first2 <app> ]

! appseq = term |
! | term Spaces term => [ first2 <app> ]
! | term Spaces term Spaces appseq
! term = primTerm |
!

! primTerm = var | Icomb

! term = primTerm |
!
