USING: accessors arrays chr colors.constants combinators io.styles
kernel lexer match parser prettyprint.backend prettyprint.custom
prettyprint.sections sequences words words.symbol ;

IN: chr.parser

! Lexical representation
: parse-array ( end -- seq )
    parse-until [ f ] [ >array ] if-empty ;

! This needs to have the constraint class already defined!
SYNTAX: P{ \ } parse-array pred>constraint suffix! ;

SYMBOLS: | -- // ;
: parse-chr-rule ( delim -- heads nkept guard body )
    [ \ // parse-array dup length [ \ -- parse-array append ] dip \ | parse-array ] dip parse-array
    [ t ] when-empty ;

SYNTAX: CHR{ \ } parse-chr-rule chr new-chr suffix! ;

SYNTAX: CHR: scan-token "@" expect \ ; parse-chr-rule <named-chr> suffix! ;

! Explicit instantiation.  These create fresh bindings for the variables before the bar
! This happens after substitution
! instance{ a b c d | rules }
SYNTAX: gen{ \ | parse-until \ } parse-until <generator> suffix! ;
M: generator pprint* pprint-object ;
M: generator pprint-delims drop \ gen{ \ } ;
M: generator >pprint-sequence
    [ vars>> \ | suffix ] [ body>> ] bi append ;

SYNTAX: G{ scan-token "}" expect <gvar> suffix! ;

M: gvar pprint*
    \ G{ pprint-word
         name>> H{ { foreground COLOR: solarized-blue } } styled-text
         \ } pprint-word ;

: pprint-chr-content ( chr -- )
    { [ keep/remove [ pprint-elements \ // pprint-word ] [ pprint-elements ] bi* ]
      [ \ -- pprint-word guard>> pprint-elements \ | pprint-word ]
      [ body>> dup t = [ drop ] [ pprint-elements ] if ]
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

PREDICATE: term-var < word "term-var" word-prop ;
INSTANCE: term-var match-var

: define-term-var ( name -- )
    create-word-in [ define-symbol ] [ t "term-var" set-word-prop ] bi ;

M: term-var reset-word
    [ call-next-method ] [ f "term-var" set-word-prop ] bi ;

SYNTAX: TERM-VARS: ";" [ define-term-var ] each-token ;
