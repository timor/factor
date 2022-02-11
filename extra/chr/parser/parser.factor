USING: accessors arrays assocs chr chr.modular colors.constants combinators
hashtables io.styles kernel lexer match namespaces parser prettyprint.backend
prettyprint.custom prettyprint.sections sequences vocabs.parser words
words.symbol ;

IN: chr.parser

! Lexical representation
: parse-array ( end -- seq )
    parse-until [ f ] [ >array ] if-empty ;

! This needs to have the constraint class already defined!
SYNTAX: P{ \ } parse-array pred>constraint suffix! ;

SYMBOLS: | -- // ;
: parse-chr-rule ( delim -- heads nkept guard body )
    [ \ // parse-array dup length [ \ -- parse-array append ] dip \ | parse-array ] dip parse-array ;

SYNTAX: CHR{ \ } parse-chr-rule chr new-chr suffix! ;

SYNTAX: CHR: scan-token "@" expect \ ; parse-chr-rule <named-chr> suffix! ;

! TODO: move to chr vocab
PREDICATE: term-var < word "term-var" word-prop ;
INSTANCE: term-var match-var

: define-term-var ( name -- )
    create-word-in [ define-symbol ] [ t "term-var" set-word-prop ] bi ;

M: term-var pprint*
    name>> H{ { foreground COLOR: solarized-blue } } styled-text ;

M: term-var reset-word
    [ call-next-method ] [ f "term-var" set-word-prop ] bi ;

SYNTAX: TERM-VARS: ";" [ define-term-var ] each-token ;

: <term-var> ( name -- var )
    <uninterned-word>
    dup t "term-var" set-word-prop ;

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

SYNTAX: G{ scan-token "}" expect <gvar> suffix! ;

M: gvar pprint*
    \ G{ pprint-word
         name>> H{ { foreground COLOR: solarized-blue } } styled-text
         \ } pprint-word ;

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
    parse-array dup [ chr? ] all? [ "invalid-chr-prog" throw ] unless ;

! * CHRat Contract

SYNTAX: IMPORT: scan-word chrat-imports [ swap suffix ] change ;

SYNTAX: CHRAT: scan-new-word
    "{" expect \ } parse-array
    f chrat-imports [ \ ; parse-chr-body
          define-chrat-prog ] with-variable ;
