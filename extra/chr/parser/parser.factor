USING: accessors arrays assocs chr chr.modular chr.state.private classes
classes.algebra classes.tuple combinators combinators.short-circuit
generalizations generic hashtables kernel lexer lists lists.private make math
namespaces parser prettyprint.backend prettyprint.custom prettyprint.sections
quotations sequences terms vocabs.parser words ;

IN: chr.parser

! Lexical representation
: parse-array ( end -- seq )
    parse-until [ f ] [ >array ] if-empty ;

! This needs to have the constraint class already defined!
SYNTAX: P{ \ } parse-array pred>constraint suffix! ;

SYMBOL: chr-prefix
SYMBOL: chr-suffix
SYMBOL: chr-modifier
! This is a short-hand for adding preds left of // to every following rule
SYNTAX: PREFIX-RULES: scan-object chr-prefix set ;
! This is a short-hand for adding preds to the body of every following rule
SYNTAX: SUFFIX-RULES: scan-object chr-suffix set ;
SYNTAX: MODIFY: scan-object chr-modifier set ;
SYMBOL: defined-existentials
SYMBOLS: | -- // ;
: apply-modifier ( heads -- heads )
    chr-modifier get [ call( heads -- heads ) ] when* ;

: parse-chr-rule ( delim -- heads nkept guard body existentials )
    f defined-existentials [
        [ \ // parse-array
          chr-prefix get prepend
          dup length [ \ -- parse-array append ] dip \ | parse-array ] dip parse-array
          chr-suffix get append
          apply-modifier
        defined-existentials get
    ] with-variable ;

SYNTAX: CHR{ \ } parse-chr-rule chr new-chr suffix! ;

SYNTAX: CHR: scan-token "@" expect \ ; parse-chr-rule named-chr new-chr swap >>rule-name suffix! ;

: set-binding ( val var -- ) current-bindings get-global set-at ;

: make-binder ( vars -- quot )
    [ <reversed> [ 1 + swap '[ _ npick _ set-binding ] % ] each-index ] [ ] make ;

: term-var-list ( spec -- seq )
    dup sequence? [ 1array ] unless
    [ term-var check-instance ] map ;

SYNTAX: :>> scan-object term-var-list
    [ defined-existentials [ swap append ] change ]
    [ make-binder append! ] bi ;

! Explicit instantiation.  These create fresh bindings for the variables before the bar
! This happens after substitution
! instance{ a b c d | rules }
SYNTAX: gen{ \ | parse-array \ } parse-array <generator> suffix! ;
SYNTAX: GEN{ "|" [ dup <term-var> 2array ] map-tokens >hashtable
             [ values ] keep [ \ } parse-array ] with-words <generator> suffix! ;
M: generator pprint* pprint-object ;
M: generator pprint-delims drop \ gen{ \ } ;
M: generator >pprint-sequence
    [ vars>> \ | suffix ] [ body>> ] bi suffix ;

SYNTAX: G{ scan-token "}" expect <term-var> suffix! ;

SYNTAX: ={ scan-object scan-object "}" expect <eq-constraint> suffix! ;
M: eq-constraint pprint* pprint-object ;
M: eq-constraint pprint-delims drop \ ={ \ } ;
M: eq-constraint >pprint-sequence tuple-slots ;

! Disjunctions
SYNTAX: Or{ \ } parse-array [ pred>constraint ] map chr-or boa suffix! ;
! SYNTAX: Cond{ \ } parse-array [ pred>constraint ] map chr-branch boa suffix! ;
SYNTAX: Cases{ \ } parse-array Cases boa suffix! ;
SYNTAX: Cond{ \ } parse-array chr-branch boa suffix! ;
M: chr-branch pprint* pprint-object ;
M: chr-branch pprint-delims drop \ Cond{ \ } ;
M: chr-branch >pprint-sequence cases>> ;
M: Cases pprint* pprint-object ;
M: Cases pprint-delims drop \ Cases{ \ } ;
M: Cases >pprint-sequence cases>> ;
SYNTAX: Assume{ scan-object \ } parse-array [ pred>constraint ] map chr-scope boa suffix! ;

! Helper
TUPLE: fake-chr-pred-cons < cons-state ;

SYNTAX: <={ scan-class parse-list-literal dup nil? [ drop __ ] when <chr-sub-pred> suffix! ;

M: fake-chr-pred-cons pprint-delims drop \ <={ \ } ;

M: chr-sub-pred pprint*
    nesting-limit? [ call-next-method ]
    [
        [ class>> ] [ args>> ] bi fake-chr-pred-cons boa
        pprint*
    ] if ;

! SYNTAX: SUB: scan-object scan-class scan-object <chr-sub-pred> suffix! ;
SYNTAX: AS: scan-object scan-object <as-pred> suffix! ;

M: as-pred pprint* \ AS: pprint-word [ var>> pprint* ] [ pred>> pprint* ] bi ;

SYNTAX: is{ scan-token <term-var> scan-object "}" expect
        callable check-instance <is-val> suffix! ;

: pprint-chr-content ( chr -- )
    { [ keep/remove [ pprint-elements \ // pprint-word ] [ pprint-elements ] bi* ]
      [ \ -- pprint-word guard>> pprint-elements \ | pprint-word ]
      ! [ body>> dup t = [ drop ] [ pprint-elements ] if ]
      [ body>> pprint-elements ]
    } cleave ;

: pprint-chr ( chr -- )
    <flow \ CHR{ pprint-word
                 pprint-chr-content
    \ } pprint-word block> ;

M: chr pprint* <flow \ CHR{ pprint-word pprint-chr-content \ } pprint-word block> ;
M: named-chr pprint* <flow \ CHR: pprint-word [ rule-name>> text "@" text ] keep
    pprint-chr-content \ ; pprint-word block> ;

M: chr-pred pprint* pprint-object ;
M: chr-pred pprint-delims drop \ P{ \ } ;
M: chr-pred >pprint-sequence [ constraint-args ] [ constraint-type prefix ] bi ;
M: C >pprint-sequence tuple-slots C prefix ;

: parse-chr-body ( end -- seq )
    parse-array dup [ { [ chr? ] [ import-solver? ] } 1|| ] all? [ "invalid-chr-prog" throw ] unless ;

! * Syntax helper
SYMBOL: UNK
<<
: term-delims-pprinter ( reader -- quot )
    '[ drop _ \ } ] ;
: parse-term ( accum class -- accum )
    \ } parse-until swap slots>tuple suffix! ;
:: make-term-constructor ( class -- )
    class name>> "{" append create-word-in :> reader
    reader [ class parse-term ] define-syntax
    class \ pprint* create-method [ pprint-object ] define
    class \ pprint-delims create-method reader term-delims-pprinter define
    class \ >pprint-sequence create-method [ tuple-slots ] define ;

SYNTAX: constructor last-word make-term-constructor ;
>>

<<
\ Is make-term-constructor
>>

M: Is pprint-delims dup class-of Is class=
    [ drop \ Is{ \ } ]
    [ call-next-method ] if ;
M: Is >pprint-sequence dup class-of Is class=
    [ tuple-slots ]
    [ call-next-method ] if ;

! * CHRat Contract

! SYNTAX: IMPORT: scan-word chrat-imports [ swap suffix ] change ;
SYNTAX: IMPORT: scan-word <import-solver> suffix! ;

SYNTAX: CHRAT: scan-new-word
    "{" expect \ } parse-array
    f chr-prefix set
    f chr-suffix set
    f chr-modifier set
    \ ; parse-chr-body define-chrat-prog ;
    ! f chrat-imports [ \ ; parse-chr-body
    !       define-chrat-prog ] with-variable ;
