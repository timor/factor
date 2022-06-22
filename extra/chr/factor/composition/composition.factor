USING: accessors arrays chr chr.factor chr.parser chr.state
combinators.short-circuit generic kernel lists math quotations sequences sets
terms words words.symbol kernel.private ;

IN: chr.factor.composition

PREDICATE: callable-word < word { [ symbol? not ] } 1&& ;

! * Compositional approach

TUPLE: Eval < chr-pred code stack ;
TUPLE: Effect < chr-pred in out preds ;
TUPLE: TypeOf < chr-pred thing type ;
TUPLE: ?TypeOf < chr-pred thing ;
TUPLE: ComposeType < chr-pred q1 q2 q3 ;
TUPLE: ApplyEffect < chr-pred effect stack ;
TUPLE: RebuildEffect < chr-pred e1 e2 target ;
TUPLE: MakeEffect < chr-pred in out preds target ;
TUPLE: Instance < chr-pred id type ;
TUPLE: Label < chr-pred stack label ;
! TUPLE: CallEffect < chr-pred effect in out ;
TUPLE: Call < chr-pred thing in out ;
TUPLE: Xor < chr-pred type1 type2 ;
TUPLE: Bind < chr-pred in outs ;
TUPLE: Drop < chr-pred val ;


: word-alias ( word -- def/f )
    H{
        { rot [ [ swap ] dip swap ] }
        { over [ swap dup [ swap ] dip ] }
        { call [ (call) ] }
    } at ;

CHRAT: chr-comp { TypeOf }

! Tag-level concrete type!
CHR: unique-type @ { TypeOf ?x ?tau } // { TypeOf ?x ?sig } -- | [ ?tau ?sig ==! ] ;

CHR: start-type-of @ // { ?TypeOf ?q } -- | { TypeOf ?q ?tau } ;

CHR: alias-type-defined @ { TypeOf ?w ?tau } // -- [ ?w word-alias :>> ?q ] |
{ TypeOf ?q ?tau } ;

CHR: type-of-prim-call @ // { TypeOf (call) ?tau } -- |
[ ?tau P{ Effect L{ ?q . ?a } ?b { P{ Call ?q ?a ?b } } } ==! ] ;
! [ ?tau P{ Effect L{ ?q . ?a } ?b { P{ Instance ?q P{ Effect ?a ?b f } } } } ==! ] ;

CHR: type-of-dip @ // { TypeOf dip ?tau } -- |
[ ?tau P{ Effect L{ ?q ?x . ?a } L{ ?x . ?b } { P{ Call ?q ?a ?b } } } ==! ] ;
! [ ?tau P{ Effect L{ ?q ?x . ?a } L{ ?x . ?b } { P{ Instance ?q P{ Effect ?a ?b f } } } } ==! ] ;

CHR: type-of-dup @ // { TypeOf [ dup ] ?tau } -- |
[ ?tau P{ Effect L{ ?x . ?a } L{ ?y ?z . ?a } { P{ Bind ?x { ?y ?z } } } } ==! ] ;

CHR: type-of-drop @ // { TypeOf [ drop ] ?tau } -- |
[ ?tau P{ Effect L{ ?x . ?a } ?a { P{ Drop ?x } } } ==! ] ;

CHR: type-of-swap @ // { TypeOf swap ?tau } -- |
[ ?tau P{ Effect L{ ?x ?y . ?a } L{ ?y ?x . ?a } f } ==! ] ;

CHR: type-of-word-call @ { TypeOf [ ?w ] ?tau } // -- [ ?w callable-word? ] |
! { TypeOf ?w ?rho }
{ TypeOf ?w ?tau } ;
! { ComposeType P{ Effect ?a ?a f } ?rho ?tau } ;

CHR: type-of-unit @ { TypeOf [ ?v ] ?tau } // -- [ ?v callable-word? not ]
|
{ TypeOf ?v ?rho }
{ MakeEffect ?a L{ ?x . ?a } { P{ Instance ?x ?rho } } ?tau } ;

CHR: type-of-val @ // { TypeOf A{ ?v } ?tau } -- [ ?v callable? not ] [ ?v callable-word? not ]
|
! { Instance ?tau W{ ?v } } ;
[ ?tau W{ W{ ?v } } ==! ] ;

CHR: type-of-word @ { TypeOf ?w ?tau } // -- [ ?w word-alias not ] [ ?w callable-word? ] [ ?w generic? not ] [ ?w def>> :>> ?q ] |
{ TypeOf ?q ?rho }
{ ComposeType P{ Effect ?a ?a { P{ Label ?a ?w } } } ?rho ?tau }
    ;

CHR: type-of-empty-quot @ // { TypeOf [ ] ?tau } -- | [ ?tau P{ Effect ?a ?a f } ==! ] ;

CHR: type-of-quot @ { TypeOf ?q ?tau } // -- [ ?q callable? ] [ ?q length 1 > ] [ ?q dup length 2 /i cut :>> ?y drop :>> ?x drop t ] |
{ TypeOf ?x ?rho }
{ TypeOf ?y ?sig }
{ ComposeType ?rho ?sig ?tau } ;

CHR: compose-effects @ // { ComposeType P{ Effect ?a ?b ?k } P{ Effect ?c ?d ?l } ?tau } -- |
[| |
 P{ Effect ?a ?b ?k } fresh :> e1
 P{ Effect ?c ?d ?l } fresh :> e2
 P{ RebuildEffect e1 e2 ?tau }
] ;

! ** Start Reasoning
CHR: rebuild-effect @ // { RebuildEffect P{ Effect ?a ?b ?k } P{ Effect ?c ?d ?l } ?tau } -- |
[ ?b ?c ==! ]
[ ?k ]
[ ?l ]
{ MakeEffect ?a ?d f ?tau } ;

CHR: unique-bind-is-same @ // { Bind ?x { ?y } } -- | [ ?x ?y ==! ] ;

CHR: drop-cancels-bind @ // { Drop ?x } { Bind ?a ?l } -- [ ?x ?l in? ]
[ ?x ?l remove :>> ?k ] |
{ Bind ?a ?k } ;


! NOTE: These only meet in renamed form
CHR: call-eats-effect @ // { Call ?q ?a ?b } { Instance ?q P{ Effect ?c ?d ?l } } -- |
[ { ?a ?b } { ?c ?d } ==! ]
[ ?l ] ;


! ** Post-Reasoning
UNION: body-pred Instance Label Call Bind Drop ;

CHR: collect-body-pred @ // { MakeEffect ?a ?b ?l ?tau } AS: ?p <={ body-pred } -- [ ?p vars ?a vars ?b vars union subset? ]
[ ?l ?p suffix :>> ?k ]
|
{ MakeEffect ?a ?b ?k ?tau } ;


CHR: finish-effect @ // { MakeEffect ?a ?b ?l ?tau } -- |
[ ?tau P{ Effect ?a ?b ?l } ==! ] ;

;


: qt ( quot -- res )
    ?TypeOf boa 1array chr-comp swap [ run-chr-query store>> ] with-var-names ;
