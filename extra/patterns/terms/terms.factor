USING: accessors arrays assocs classes combinators combinators.short-circuit
hashtables kernel lexer lists make match math namespaces parser
prettyprint.backend prettyprint.custom prettyprint.sections quotations sequences
sets typed types.util vectors vocabs.parser words words.constant ;

IN: patterns.terms

FROM: syntax => _ ;
! Factorization protocol
MIXIN: app-term
GENERIC: left/right ( app -- left right )
GENERIC: head-term ( term -- term )
GENERIC: new-app-term ( left right exemplar -- app-term )

INSTANCE: cons-state app-term
M: cons-state left/right uncons ;
M: cons-state head-term car ;
M: cons-state new-app-term drop
    cons ;

! Head sequence
UNION: array-like array slice ;
PREDICATE: app-seq < array-like length 1 > ;
PREDICATE: head-seq < array-like length 1 = ;
INSTANCE: app-seq app-term
GENERIC: maybe-unseq ( seq -- term )
M: head-seq maybe-unseq first ;
M: object maybe-unseq ;
M: vector maybe-unseq >array maybe-unseq ;
M: app-seq head-term first ;
M: app-seq left/right
    unclip-last-slice
    [ maybe-unseq ] dip ;
GENERIC: maybe-seq ( obj -- seq )

M: array-like maybe-seq ;
M: object maybe-seq 1array ;
M: app-seq new-app-term
    '[ maybe-seq _ like ] dip suffix ;

SINGLETON: nomatch

: <upsym> ( name -- pattern-symbol )
    uvar <uninterned-word> [ t "pattern-symbol" set-word-prop ] keep ;

: <psym> ( name -- pattern-symbol )
    f <word> dup t "pattern-symbol" set-word-prop ;

PREDICATE: pattern-symbol < word "pattern-symbol" word-prop? ;
INSTANCE: pattern-symbol match-var
! Wildcard
SINGLETON: __

PREDICATE: host-constructor < word { [ __? ] [ match-var? ] } 1|| not ;

TUPLE: pcase pattern body ;
C: <pcase> pcase
TUPLE: special-pcase < pcase rest ;
C: <special-pcase> special-pcase

SYMBOL: ->
SYMBOL: |
SYNTAX: P{ -> parse-until \ } parse-until [ maybe-unseq ] bi@ <pcase> suffix! ;
M: pcase pprint* pprint-object ;
M: pcase pprint-delims drop \ P{ \ } ;
M: pcase >pprint-sequence
    [ pattern>> ] [ body>> ] bi
    [ maybe-seq ] bi@ { -> } glue ;

! Dynamic match case structure
TUPLE: case { binding-syms sequence } pattern body ;
C: <case> case
TUPLE: special-dcase < case rest ;
C: <special-dcase> special-dcase


MIXIN: reduction-defined
PREDICATE: pattern-def < constant "constant" word-prop
    { [ case? ] [ pcase? ] } 1|| ;
PREDICATE: term-def < word "pattern" word-prop ;
INSTANCE: term-def reduction-defined
INSTANCE: pattern-def reduction-defined
INSTANCE: case reduction-defined
INSTANCE: pcase reduction-defined

GENERIC: >pattern ( obj -- pattern/f )
M: object >pattern ;
M: pattern-def >pattern "constant" word-prop >pattern ;
M: term-def >pattern "pattern" word-prop ;
! M: pcase >pattern ;

! "Wrapper" around other words
TUPLE: match-sym word ;
C: <msym> match-sym

SYNTAX: M< scan-object ">" expect match-var check-instance <msym> suffix! ;
M: match-sym pprint*
    \ M< pprint-word
    word>> pprint*
    ">" text ;


! TUPLE: special-pcase pcase default ;
! C: <special-pcase> special-pcase
! Cond structure
! : <extension> ( cases default -- case )
!     [ <reversed> ] dip
!     [ first2 <pcase> swap <special-pcase> ] reduce ;

:: (desugar-special-pcase) ( p s r -- pattern )
    "x" <upsym> :> x
    "y" <upsym> :> y
    "z" <upsym> :> z
    x
    { nomatch y } y <pcase>
    p z { nomatch s } <pcase> <pcase> x { r x } 3array
    2array <pcase> ;

: <extension> ( cases default -- case )
    [ <reversed> ] dip
    [ first2 rot <special-pcase> ] reduce ;

SYNTAX: Ext{ -> parse-until \ | parse-until \ } parse-until
    [ maybe-unseq ] tri@ <special-pcase> suffix! ;

M: special-pcase pprint-delims drop \ Ext{ \ } ;
M: special-pcase >pprint-sequence
    [ call-next-method \ | suffix ]
    [ rest>> suffix ] bi ;

: <dlam> ( var body -- term )
    [ [ 1array ] [ <msym> ] bi ] dip <case> ;

:: (desugar-dynamic-special-case) ( theta p s r -- term  )
    "x" <upsym> :> x
    x <msym> :> xhat
    "y" <upsym> :> y
    y <msym> :> yhat
    "z" <upsym> :> z
    z <msym> :> zhat
    x
    y 1array { nomatch yhat } y <case>
    theta p z { nomatch s } <dlam> <case> x { r x } 3array
    2array <dlam> ;

! NOTE: memoizing this to be able to catch fixpoints?
MEMO: desugar-special-pcase ( special-pcase -- pattern )
    [ pattern>> ] [ body>> ] [ rest>> ] tri
    (desugar-special-pcase) ;

MEMO: desugar-special-dcase ( special-dcase -- pattern )
    { [ binding-syms>> ] [ pattern>> ] [ body>> ] [ rest>> ] } cleave
    (desugar-dynamic-special-case) ;

M: special-pcase >pattern
    desugar-special-pcase ;
M: special-dcase >pattern
    desugar-special-dcase ;
M: case >pattern ;

: build-case-ext ( accum bindings lhs rhs cont -- accum )
    [ <case> ]
    [ maybe-unseq <special-dcase> ] if-empty suffix! ;

SYNTAX: P<
    "[" expect "]" [ dup <psym> 2array ] map-tokens >hashtable
    [ values ] keep
    [ -> parse-until maybe-unseq
      | parse-until maybe-unseq
      \ > parse-until ] with-words build-case-ext ;

SYNTAX: lam{ scan-token [ <psym> ] keep [ drop 1array ] [ drop <msym> ] [ associate ] 2tri
             [ \ } parse-until maybe-unseq ] with-words
    f build-case-ext ;

: >pprint-dcase-seq ( bindings lhs rhs -- seq )
    [
        [ >quotation , ]
        [ % -> , ]
        [ % | , ] tri*
    ] { } make ;

M: case pprint* pprint-object ;
M: case pprint-delims drop \ P< \ > ;
M: case >pprint-sequence
    [ binding-syms>> ] [ pattern>> ] [ body>> ] tri
    [ maybe-seq ] bi@ >pprint-dcase-seq ;

SYMBOL: assume-alpha=?

! TODO: this is probably wrong!
: naive-alpha= ( case1 case2 -- ? )
    assume-alpha=? [ match ] with-variable-off
    {
      [ ]
      [ [ [ match-var? ] both? ] assoc-all? ]
      [ [ keys ] [ values ] bi intersects? not ]
    } 1&& ;

M: case equal?
    assume-alpha=? get
    [ naive-alpha= ]
    [ call-next-method ] if ;

: with-alpha= ( quot -- )
    assume-alpha=? swap with-variable-on ; inline

M: special-dcase >pprint-sequence
    [ call-next-method ]
    [ rest>> maybe-seq append ] bi ;

PREDICATE: case-def < constant "constant" word-prop case? ;

! Result of applying match, which must be turned into a match-application
SINGLETONS: undefined none ;
UNION: match-result assoc undefined none ;

PREDICATE: host-data < object { [ app-term? not ] [ match-var? not ] [ reduction-defined? not ]
                                [ match-sym? not ]
    } 1&& ;

! Result of rule application, which can be acted upon to modify the term
TUPLE: subst-app subst term ;
C: <subst-app> subst-app
UNION: match-app subst-app nomatch ;

TYPED: disjoint-domains? ( s1: assoc s2: assoc -- ? )
    [ keys ] bi@ intersects? not ;

TYPED: match-disjoint-union ( m1: match-result m2: match-result -- m: match-result )
    {
        { [ 2dup [ undefined? ] either? ] [ 2drop undefined ] }
        { [ 2dup { [ [ assoc? ] both? ] [ disjoint-domains? ] } 2&& ]
          [ assoc-union ] }
        [ 2drop none ]
    } cond ;

GENERIC#: match-rule 1 ( match-result term -- match-app )
M: assoc match-rule <subst-app> ;
M: none match-rule 2drop nomatch ;
ERROR: undefined-match term ;
M: undefined match-rule undefined-match ;
