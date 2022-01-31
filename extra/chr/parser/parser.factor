USING: accessors arrays chr classes colors.constants combinators io.styles
kernel lexer parser prettyprint.backend prettyprint.custom prettyprint.sections
quotations sequences ;

IN: chr.parser
: parse-array ( end -- seq )
    parse-until [ f ] [ >array ] if-empty ; inline

SYMBOLS: | -- // ;
: parse-chr-rule ( delim -- heads nkept guard body )
    [ \ // parse-array dup length [ \ -- parse-array append ] dip \ | parse-array ] dip parse-array
    [ t ] when-empty ;

SYNTAX: CHR{ \ } parse-chr-rule chr new-chr suffix! ;
SYNTAX: ={ scan-object scan-object "}" expect <eq> suffix! ;
SYNTAX: is={ scan-object scan-object callable check-instance "}" expect <set-eq> suffix! ;
SYNTAX: 2{ scan-class [ scan-object scan-object ] dip "}" expect new-binary-constraint suffix! ;

SYNTAX: CHR: scan-token "@" expect \ ; parse-chr-rule <named-chr> suffix! ;

M: binary-constraint pprint* pprint-object ;
M: binary-constraint pprint-delims drop \ 2{ \ } ;
: pprint-binary-args ( binary-constraint -- seq )
    [ v1>> ] [ v2>> ] bi 2array ;

M: binary-constraint >pprint-sequence
    [ pprint-binary-args ] [ class-of prefix ] bi ;

M: eq pprint-delims drop \ ={ \ } ;
M: eq >pprint-sequence pprint-binary-args ;
M: set-eq pprint-delims drop \ is={ \ } ;
M: set-eq >pprint-sequence pprint-binary-args ;

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
