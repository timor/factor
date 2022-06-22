USING: accessors arrays assocs chr chr.factor chr.parser chr.state
combinators.short-circuit generic kernel kernel.private lists math quotations
sequences sets terms words words.symbol ;

IN: chr.factor.composition

PREDICATE: callable-word < word { [ symbol? not ] } 1&& ;

! * Compositional approach

TUPLE: Eval < chr-pred code stack ;
TUPLE: Effect < chr-pred in out preds ;
TUPLE: TypeOf < chr-pred thing type ;
TUPLE: ?TypeOf < chr-pred thing ;

! States that q3 is the composition of q1 and q2
TUPLE: ComposeType < chr-pred q1 q2 q3 ;

! Actually triggers computing composed effect and storing it into target
TUPLE: ComposeEffect < chr-pred e1 e2 target ;
TUPLE: MakeEffect < chr-pred in out locals preds target ;
TUPLE: Instance < chr-pred id type ;
! For destructuring
TUPLE: Label < chr-pred stack label ;
TUPLE: Literal < chr-pred val ;

TUPLE: CallEffect < chr-pred thing in out ;
TUPLE: Xor < chr-pred type1 type2 ;
TUPLE: And < chr-pred types ;
! TUPLE: Intersection < chr-pred type types ;
TUPLE: Intersection < chr-pred type types ;
TUPLE: Union < chr-pred type types ;
TUPLE: SubType < chr-pred sub super ;

TUPLE: Bind < chr-pred in outs ;
TUPLE: Drop < chr-pred val ;
TUPLE: Use < chr-pred val ;
TUPLE: Let < chr-pred var val type ;


: word-alias ( word -- def/f )
    H{
        { rot [ [ swap ] dip swap ] }
        { over [ swap dup [ swap ] dip ] }
        { call [ (call) ] }
        { nip [ [ drop ] dip ] }
        { 2drop [ drop drop ] }
        { 2dup [ over over ] }
        { -rot [ swap [ swap ] dip ] }
    } at ;

CHRAT: chr-comp { TypeOf }

! Tag-level concrete type!
CHR: unique-type @ { TypeOf ?x ?tau } // { TypeOf ?x ?sig } -- | [ ?tau ?sig ==! ] ;

CHR: start-type-of @ // { ?TypeOf ?q } -- | { TypeOf ?q ?tau } ;

CHR: alias-type-defined @ { TypeOf ?w ?tau } // -- [ ?w word-alias :>> ?q ] |
{ TypeOf ?q ?tau } ;

CHR: type-of-prim-call @ // { TypeOf (call) ?tau } -- |
[ ?tau P{ Effect L{ ?q . ?a } ?b { P{ CallEffect ?q ?a ?b } } } ==! ] ;
! [ ?tau P{ Effect L{ ?q . ?a } ?b { P{ Instance ?q P{ Effect ?a ?b f } } } } ==! ] ;

CHR: type-of-dip @ // { TypeOf dip ?tau } -- |
[ ?tau P{ Effect L{ ?q ?x . ?a } L{ ?x . ?b } { P{ CallEffect ?q ?a ?b } } } ==! ] ;
! [ ?tau P{ Effect L{ ?q ?x . ?a } L{ ?x . ?b } { P{ Instance ?q P{ Effect ?a ?b f } } } } ==! ] ;

! CHR: type-of-dup @ // { TypeOf [ dup ] ?tau } -- |
CHR: type-of-dup @ // { TypeOf dup ?tau } -- |
[ ?tau P{ Effect L{ ?x . ?rho } L{ ?y ?z . ?rho } {
              P{ Bind ?x { ?y ?z } }
              ! P{ TypeOf ?x ?c }
              ! P{ TypeOf ?y ?a }
              ! P{ TypeOf ?z ?b }
              ! P{ SubType ?c ?a }
              ! P{ SubType ?c ?b }
          } }
  ==! ] ;

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
{ MakeEffect ?a L{ ?x . ?a } f { P{ Instance ?x ?rho } P{ Literal ?x } } ?tau } ;

CHR: type-of-val @ // { TypeOf A{ ?v } ?tau } -- [ ?v callable? not ] [ ?v callable-word? not ]
|
! { Instance ?tau W{ ?v } } ;
[ ?tau W{ W{ ?v } } ==! ] ;

CHR: type-of-word @ { TypeOf A{ ?w } ?tau } // -- [ ?w word-alias not ] [ ?w callable-word? ] [ ?w generic? not ] [ ?w def>> :>> ?q ] |
! { TypeOf ?q ?rho }
! { ComposeType P{ Effect ?a ?a { P{ Label ?a ?w } } } ?rho ?tau }
{ TypeOf ?q ?tau }
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
 P{ ComposeEffect e1 e2 ?tau }
] ;

! ** Start Reasoning
UNION: body-pred Instance Label CallEffect Bind Drop Use Literal ;

CHR: rebuild-compose-effect @ // { ComposeEffect P{ Effect ?a ?b ?k } P{ Effect ?c ?d ?l } ?tau } -- |
[ ?b ?c ==! ]
[ ?k ]
[ ?l ]
{ MakeEffect ?a ?d f f ?tau } ;

! ** Simplification/Intra-Effect reasoning

CHR: unique-bind-is-same @ // { Bind ?x { ?y } } -- | [ ?x ?y ==! ] ;

CHR: central-bind-point @ // { Bind ?x ?l } { Bind ?a ?k } -- [ ?a ?l in? ]
[ ?a ?l remove ?k union :>> ?m ] |
{ Bind ?x ?m } ;

CHR: drop-cancels-bind @ // { Drop ?x } { Bind ?a ?l } -- [ ?x ?l in? ]
[ ?x ?l remove :>> ?k ] |
{ Bind ?a ?k } ;

CHR: drop-cancels-lit @ // { Drop ?x } { Instance ?x __ } { Literal ?x } -- | ;

CHR: use-cancels-bind @ // { Use ?x } { Bind ?a ?l } -- [ ?x ?l in? ]
[ ?x ?l remove :>> ?k ] |
{ Bind ?a ?k } ;

CHR: bind-propagates-literals @ // { Bind ?x ?l } { Literal ?x } { Instance ?x ?tau } -- [ { ?tau } first :>> ?c ] |
[ ?l [ { ?c } first fresh Instance boa ] map ]
[ ?l [ Literal boa ] map ] ;

! CHR: same-lit-is-same-var @ { Literal ?x } { Instance ?x A{ ?v } } // { Literal ?y } { Instance ?y A{ ?v } } -- |
! [ ?x ?y ==! ] ;

! NOTE: These only meet in renamed form?
CHR: call-eats-effect @ // { Literal ?q } { Instance ?q P{ Effect ?c ?d ?l } } { CallEffect ?q ?a ?b } -- |
[ { ?a ?b } { ?c ?d } ==! ]
[ ?l ] ;
! CHR: call-applies-effect @ { CallEffect ?q ?a ?b } { Instance ?q P{ Effect ?c ?d ?l } } // -- |
! [ { ?a ?b } { ?c ?d } ==! ]
! [ ?l ]
! { Use ?q } ;

! CHR: used-instance @ { Use ?q } { Instance ?q __ }

! ** Post-Reasoning

! Unused calls define Effects

: effect-vars ( make-effect -- set )
    [ in>> vars ] [ out>> vars union ] [ locals>> vars union ] tri ;

! existentials
CHR: collect-type-ofs @ // AS: ?e P{ MakeEffect ?a ?b ?x ?l ?tau } { TypeOf ?v ?rho } --
[ ?v ?e effect-vars in? ]
[ ?l P{ TypeOf ?v ?rho } suffix :>> ?k ] |
{ MakeEffect ?a ?b ?x ?k ?tau } ;

CHR: collect-bind-defs-forward @ // AS: ?e P{ MakeEffect ?a ?b ?x ?l ?tau } { Bind ?c ?d } --
[ ?c ?e effect-vars in? ]
[ ?d vars ?x union :>> ?y ]
[ ?l P{ Bind ?c ?d } suffix :>> ?k ]
| { MakeEffect ?a ?b ?y ?k ?tau } ;

CHR: collect-bind-defs-backward @ // AS: ?e P{ MakeEffect ?a ?b ?x ?l ?tau } { Bind ?c ?d } --
[ ?d ?e effect-vars subset? ]
[ ?x ?c 1array union :>> ?y ]
[ ?l P{ Bind ?c ?d } suffix :>> ?k ]
| { MakeEffect ?a ?b ?y ?k ?tau } ;

CHR: collect-nested-call-effect @ // AS: ?e P{ MakeEffect ?a ?b ?x ?l ?tau } AS: ?p P{ CallEffect ?q ?rho ?sig } --
[ ?q ?e effect-vars in? ]
[ ?x ?rho vars ?sig vars union union :>> ?y ]
[ ?l ?p suffix :>> ?k ]
| { MakeEffect ?a ?b ?y ?k ?tau } ;

CHR: collect-instance @ // AS: ?e P{ MakeEffect ?a ?b ?x ?l ?tau } P{ Instance ?v ?rho } --
[ ?v ?e effect-vars in? ]
[ ?l P{ Instance ?v ?rho } suffix :>> ?k ]
| { MakeEffect ?a ?b ?x ?k ?tau } ;

CHR: collect-body-pred @ // AS: ?e P{ MakeEffect ?a ?b ?x ?l ?tau } AS: ?p <={ body-pred } -- [ ?p vars ?e effect-vars subset? ]
[ ?l ?p suffix :>> ?k ]
|
{ MakeEffect ?a ?b ?x ?k ?tau } ;


CHR: finish-effect @ // { MakeEffect ?a ?b __ ?l ?tau } -- |
[ ?tau P{ Effect ?a ?b ?l } ==! ] ;

;


: qt ( quot -- res )
    ?TypeOf boa 1array chr-comp swap [ run-chr-query store>> ] with-var-names ;
