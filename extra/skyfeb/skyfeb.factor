USING: accessors arrays assocs colors.constants combinators
combinators.short-circuit io.styles kernel lexer lists locals.rewrite make match
math namespaces parser prettyprint.backend prettyprint.custom
prettyprint.sections prettyprint.stylesheet quotations sequences strings typed
types.util variants vocabs.parser words ;

IN: skyfeb
! QUALIFIED-WITH: match pm
FROM: variants => match ;
FROM: syntax => _ ;

! * SKYFEB Calculus evaluator

VARIANT: skyfeb-term
    S K Y F E B
    var: { name }
    app: { { left } { right } }
    ;

TYPED: <fresh-var> ( name -- var: var )
    uvar <var> ;

INSTANCE: app list
M: app car left>> ;
M: app cdr right>> ;

! PREDICATE: skyfeb-atom < word "skyfeb-def" word-prop not ;
PREDICATE: skyfeb-word < word "skyfeb-def" word-prop ;
SINGLETONS: I -> || L let letrec ;
UNION: syntax-sugar I -> || L let letrec ;
! Syntax sugar, can be in parsed terms, but must be reduced

UNION: term skyfeb-term match-var syntax-sugar ;
PREDICATE: opaque-operator < object { [ skyfeb-word? ] [ term? ] } 1|| not ;
UNION: operator S K Y F E B opaque-operator ;

TYPED: arity ( op: operator -- n: integer )
    H{
        { Y 1 }
        { K 2 }
        { S 3 }
        { F 3 }
        { E 4 }
    } at ;

PREDICATE: operator-app < app left>> operator? ;

DEFER: >skyfeb
GENERIC: >skyfeb-atom ( obj -- term: term )
M: string >skyfeb-atom <var> ;
! M: object >skyfeb-atom B swap <app> ;
M: object >skyfeb-atom ;
M: syntax-sugar >skyfeb-atom ;
! M: array >skyfeb-atom nil suffix items>list >skyfeb ;
M: array >skyfeb-atom >skyfeb ;
! M: bapp-pre-term >skyfeb-atom [  ]
! M: list >skyfeb-atom >skyfeb ;
M: term >skyfeb-atom ;
! M: constant >skyfeb-atom "constant" word-prop ;

M: app rewrite-element
    dup rewrite-literal? [
        [ left>> rewrite-element ]
        [ right>> rewrite-element ] bi
        [ [ >skyfeb-atom ] bi@ <app> ] %
    ] [ , ] if ;

: seq>sf ( seq -- app )
    dup sequence? [
        dup length 1 = [ first >skyfeb-atom ]
        [ unclip-last [ seq>sf ] [ >skyfeb-atom ] bi* <app> ] if
    ] [ >skyfeb-atom ] if ;

! TYPED: >skyfeb ( list -- term: term )
: >skyfeb ( obj -- term: term )
    seq>sf ;

: n-args? ( term n -- ? )
    { { [ dup 0 = ] [ 2drop f ] }
      { [ over app? ] [ [ right>> ] dip 1 - n-args? ] }
      [ 2drop t ]
    } cond ;

GENERIC: factorable? ( term -- ? )
M: operator factorable? drop t ;
M: var factorable? drop f ;
M: operator-app factorable?
    [ right>> ] [ left>> ] bi
    dup B? [ 2drop t ]
    [ arity 1 - n-args? ] if ;
M: app factorable? drop f ;

PREDICATE: compound < operator-app factorable? ;

: parse-skyfeb-literal ( accum -- accum )
    \ } [ >skyfeb ! dup match-var? [ literalize ] when
          literalize
        ] parse-literal ;

SYNTAX: SF{  parse-skyfeb-literal ;

: scan-maybe-match-var ( -- str/var )
    scan-token dup search dup match-var? [ nip ] [ drop ] if ;
SYNTAX: VAR{ scan-maybe-match-var "}" expect <var> suffix! ;
! SYNTAX: UVAR{ scan-token "}" expect uvar <var> suffix! ;


: skyfeb>seq ( term -- elt )
    {
        { app [| left right |
               {
                   { [ left app? not ] [ left right [ skyfeb>seq ] bi@ 2array ] }
                   [ left skyfeb>seq right skyfeb>seq suffix ]
               } cond
              ] }
        [ ]
    } match ;

SYMBOL: in-pprint-skyfeb
M: app pprint*
    in-pprint-skyfeb [ pprint-object ] with-variable-on ;
M: app pprint-delims drop \ SF{ \  } ;
M: app >pprint-sequence skyfeb>seq ;
M: var pprint*
    in-pprint-skyfeb get
    [ H{ { foreground COLOR: solarized-blue } }
      base-string-style [ name>> pprint* ] with-variable ]
    [ \ VAR{ pprint-word name>> text \ } pprint-word ] if ;

SYNTAX: SKY: scan-new "{" expect [ parse-skyfeb-literal unclip-last-slice ] dip swap "skyfeb-def" set-word-prop ;
