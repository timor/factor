USING: accessors arrays assocs chr chr.modular chr.state.private classes
classes.tuple combinators hashtables kernel lexer lists lists.private namespaces
parser prettyprint.backend prettyprint.custom prettyprint.sections quotations
sequences terms vocabs.parser ;

IN: chr.parser

! Lexical representation
: parse-array ( end -- seq )
    parse-until [ f ] [ >array ] if-empty ;

! This needs to have the constraint class already defined!
SYNTAX: P{ \ } parse-array pred>constraint suffix! ;

SYMBOL: defined-existentials
SYMBOLS: | -- // ;
: parse-chr-rule ( delim -- heads nkept guard body existentials )
    f defined-existentials [
        [ \ // parse-array dup length [ \ -- parse-array append ] dip \ | parse-array ] dip parse-array
        defined-existentials get
    ] with-variable ;

SYNTAX: CHR{ \ } parse-chr-rule chr new-chr suffix! ;

SYNTAX: CHR: scan-token "@" expect \ ; parse-chr-rule named-chr new-chr swap >>rule-name suffix! ;

: ex-check-setter-quot ( var -- quot )
    '[ dup [ _ current-bindings get-global set-at ] when* ] ;

SYNTAX: :>> scan-word term-var check-instance
    [ defined-existentials [ swap suffix ] change ]
    [ ex-check-setter-quot append! ] bi
    ;

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

SYNTAX: ={ scan-object scan-object "}" eq-constraint boa suffix! ;
M: eq-constraint pprint* pprint-object ;
M: eq-constraint pprint-delims drop \ ={ \ } ;
M: eq-constraint >pprint-sequence tuple-slots ;

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

: parse-chr-body ( end -- seq )
    parse-array dup [ { [ chr? ] [ import-solver? ] } 1|| ] all? [ "invalid-chr-prog" throw ] unless ;

! * CHRat Contract

! SYNTAX: IMPORT: scan-word chrat-imports [ swap suffix ] change ;
SYNTAX: IMPORT: scan-word <import-solver> suffix! ;

SYNTAX: CHRAT: scan-new-word
    "{" expect \ } parse-array
    \ ; parse-chr-body define-chrat-prog ;
    ! f chrat-imports [ \ ; parse-chr-body
    !       define-chrat-prog ] with-variable ;
