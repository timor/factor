USING: accessors arrays assocs chr chr.factor chr.parser chr.state
classes.algebra combinators.short-circuit generic kernel kernel.private lists
math math.private quotations sequences sets terms words words.symbol ;

IN: chr.factor.composition

PREDICATE: callable-word < word { [ symbol? not ] } 1&& ;

! * Compositional approach

TUPLE: Eval < chr-pred code stack ;
TUPLE: Effect < chr-pred in out preds ;
TUPLE: TypeOf < chr-pred thing type ;
TUPLE: ?TypeOf < chr-pred thing ;


TUPLE: MakeDispatch < chr-pred cases target ;

! States that q3 is the composition of q1 and q2
TUPLE: ComposeType < chr-pred q1 q2 q3 ;

! Actually triggers computing composed effect and storing it into target
TUPLE: ComposeEffect < chr-pred e1 e2 target ;
TUPLE: MakeEffect < chr-pred in out locals preds target ;
TUPLE: Instance < chr-pred id type ;
! For destructuring
TUPLE: Label < chr-pred stack label ;
TUPLE: Literal < chr-pred val ;
TUPLE: Declare < chr-pred classes stack ;

TUPLE: CallEffect < chr-pred thing in out ;
TUPLE: MakeXor < chr-pred type1 type2 target ;
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

TUPLE: Invalid < chr-pred ;

TUPLE: Eq < chr-pred val1 val2 ;


: word-alias ( word -- def/f )
    H{
        { rot [ [ swap ] dip swap ] }
        { over [ swap dup [ swap ] dip ] }
        ! { call [ (call) ] }
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

CHR: type-of-mux @ // { TypeOf ? ?tau } -- |
[
    ?tau
    P{ Xor
       P{ Effect L{ ?q ?p ?c . ?a } L{ ?p . ?a } { P{ Instance ?c not{ W{ f } } } { Drop ?q } { Use ?c } } }
       P{ Effect L{ ?q ?p ?c . ?a } L{ ?q . ?a } { P{ Instance ?c W{ f } } { Drop ?p } { Use ?c } } }
     }
    ==!
] ;

CHR: type-of-predicate @ // { TypeOf ?w ?tau } -- [ ?w word? ] [ ?w "predicating" word-prop :>> ?c ] |
[| |
 ?c class-not :> ?d
 ?tau
  P{ Xor
     P{ Effect L{ ?x . ?a } L{ ?y . ?a } {
            P{ Instance ?x ?c }
            P{ Literal ?y }
            P{ Instance ?y W{ t } }
            P{ Use ?x }
        } }
     P{ Effect L{ ?x . ?a } L{ ?y . ?a } {
            P{ Instance ?x ?d }
            P{ Literal ?y }
            P{ Instance ?y W{ f } }
            P{ Use ?x }
        } }
   }
  ==!
] ;

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

CHR: type-of-declare @ // { TypeOf declare ?tau } -- |
[ ?tau
  P{ Effect L{ ?l . ?a } ?a {
         P{ Instance ?l array }
         P{ Declare ?l ?a }
         P{ Use ?l }
     } }
  ==! ] ;

! *** Regular words
CHR: type-of-word @ { TypeOf A{ ?w } ?tau } // -- [ ?w word-alias not ] [ ?w callable-word? ] [ ?w "predicating" word-prop not ] [ ?w generic? not ] [ ?w def>> :>> ?q ] |
! { TypeOf ?q ?rho }
! { ComposeType P{ Effect ?a ?a { P{ Label ?a ?w } } } ?rho ?tau }
{ TypeOf ?q ?tau }
    ;

CHR: type-of-generic @ { TypeOf ?w ?tau } // -- [ ?w generic? ] [ ?w "methods" word-prop sort-methods <reversed> >list :>> ?l ] |
{ MakeDispatch ?l ?tau } ;

CHR: dispatch-done @ // { MakeDispatch +nil+ ?tau } -- | [ ?tau null ==! ] ;
CHR: dispatch-case @ // { MakeDispatch L{ { ?c ?m } . ?r } ?tau } -- |
{ TypeOf ?m ?rho }
{ MakeDispatch ?r ?sig }
{ MakeXor ?rho ?sig ?tau } ;


CHR: type-of-fixnum+ @ { TypeOf fixnum+ ?tau } // -- |
[ ?tau
  P{ Effect L{ ?x ?y . ?a } L{ ?z . ?b } { P{ Instance ?x fixnum } P{ Instance ?y fixnum } P{ Use ?x } P{ Use ?y } P{ Instance ?z integer } } }
  ==!
] ;

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

CHR: compose-xor-effects-right @ // { ComposeType P{ Effect ?a ?b ?k } P{ Xor P{ Effect ?c ?d ?l } P{ Effect ?x ?y ?m } } ?tau } -- |
[| |
 P{ Effect ?a ?b ?k } fresh :> e1
 P{ Effect ?c ?d ?l } fresh :> e3
 P{ Effect ?a ?b ?k } fresh :> e2
 P{ Effect ?x ?y ?m } fresh :> e4
 {
     P{ ComposeEffect e1 e3 ?rho }
     P{ ComposeEffect e2 e4 ?sig }
     P{ MakeXor ?rho ?sig ?tau }
     ! [ ?tau P{ Xor ?rho ?sig } ==! ]
 }
] ;

CHR: compose-xor-effects-left @ // { ComposeType P{ Xor P{ Effect ?c ?d ?l } P{ Effect ?x ?y ?m } } P{ Effect ?a ?b ?k } ?tau } -- |
[| |
 P{ Effect ?c ?d ?l } fresh :> e1
 P{ Effect ?x ?y ?m } fresh :> e2
 P{ Effect ?a ?b ?k } fresh :> e3
 P{ Effect ?a ?b ?k } fresh :> e4
 {
     P{ ComposeEffect e1 e3 ?rho }
     P{ ComposeEffect e2 e4 ?sig }
     P{ MakeXor ?rho ?sig ?tau }
     ! [ ?tau P{ Xor ?rho ?sig } ==! ]
 }
] ;


CHR: compose-xor-effects-both @ // { ComposeType P{ Xor ?a ?b } P{ Xor ?c ?d } ?tau } -- |
{ ComposeType ?a P{ Xor ?c ?d } ?rho }
{ ComposeType ?b P{ Xor ?c ?d } ?sig }
{ MakeXor ?rho ?sig ?tau }
! [ ?tau P{ Xor ?rho ?sig } ==! ]
    ;


CHR: make-null-xor @ // { MakeXor null null ?tau } -- | [ ?tau null ==! ] ;
CHR: make-trivial-xor-left @ // { MakeXor ?rho null ?tau } -- | [ ?rho ?tau ==! ] ;
CHR: make-trivial-xor-right @ // { MakeXor null ?rho ?tau } -- | [ ?rho ?tau ==! ] ;
CHR: make-xor @ // { MakeXor ?rho ?sig ?tau } -- | [ ?tau P{ Xor ?rho ?sig } ==! ] ;

! ** Start Reasoning
UNION: body-pred Instance Label CallEffect Bind Drop Use Literal Declare ;

! NOTE: assumed renaming here already
CHR: rebuild-compose-effect @ // { ComposeEffect P{ Effect ?a ?b ?k } P{ Effect ?c ?d ?l } ?tau } -- |
[ ?b ?c ==! ]
[ ?k ]
[ ?l ]
{ MakeEffect ?a ?d f f ?tau } ;

! ** Simplification/Intra-Effect reasoning
CHR: early-exit @ { Invalid } // <={ body-pred } -- | ;

CHR: unique-instance @ { Instance ?x ?tau } // { Instance ?x ?tau } -- | ;

CHR: instance-intersection @ // { Instance ?x A{ ?tau } } { Instance ?x A{ ?sig } } -- [ { ?tau ?sig } first2 class-and :>> ?c ] |
{ Instance ?x ?c } ;

CHR: null-instance-is-invalid @ { Instance __ null } // -- | { Invalid } ;

CHR: unique-bind-is-same @ // { Bind ?x { ?y } } -- | [ ?x ?y ==! ] ;

CHR: central-bind-point @ // { Bind ?x ?l } { Bind ?a ?k } -- [ ?a ?l in? ]
[ ?a ?l remove ?k union :>> ?m ] |
{ Bind ?x ?m } ;

CHR: drop-cancels-bind @ // { Drop ?x } { Bind ?a ?l } -- [ ?x ?l in? ]
[ ?x ?l remove :>> ?k ] |
{ Bind ?a ?k } ;

CHR: drop-cancels-lit @ // { Drop ?x } { Instance ?x __ } { Literal ?x } -- | ;

CHR: bind-propagates-literals @ // { Bind ?x ?l } { Literal ?x } { Instance ?x ?tau } -- [ { ?tau } first :>> ?c ] |
[ ?l [ { ?c } first fresh Instance boa ] map ]
[ ?l [ Literal boa ] map ] ;

CHR: bind-propagates-instance @ { Bind ?x ?l } { Instance ?x ?tau } // -- [ { ?tau } first :>> ?c ] |
[ ?l [ { ?c } first fresh Instance boa ] map ] ;

CHR: bind-backprops-instance @ { Bind ?x ?l } { Instance ?v ?tau } // -- [ ?v ?l in? ] [ { ?tau } first :>> ?c ] |
{ Instance ?x ?tau } ;

CHR: used-propagated-instance @ { Use ?x } { Bind __ ?l } // { Instance ?x __ } -- [ ?x ?l in? ] | ;

CHR: use-cancels-bind @ // { Use ?x } { Bind ?a ?l } -- [ ?x ?l in? ]
[ ?x ?l remove :>> ?k ] |
{ Bind ?a ?k } ;

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

CHR: did-declare @ // { Declare +nil+ __ } -- | ;
CHR: do-declare @ // { Declare L{ ?tau . ?r } L{ ?x . ?xs } } -- |
{ Instance ?x ?tau }
{ Declare ?r ?xs } ;

CHR: known-declare @ { Declare ?l ?a } { Literal ?l } { Instance ?l ?tau } // -- |
[ ?l ?tau <reversed> >list ==! ] ;

CHR: used-literal @ // { Use ?x } { Literal ?x } { Instance ?x __  } -- | ;

! ** Post-Reasoning

! Unused calls define Effects

: effect-vars ( make-effect -- set )
    [ in>> vars ] [ out>> vars union ] [ locals>> vars union ] tri ;

! existentials
! CHR: collect-type-ofs @ // AS: ?e P{ MakeEffect ?a ?b ?x ?l ?tau } { TypeOf ?v ?rho } --
! [ ?v ?e effect-vars in? ]
! [ ?l P{ TypeOf ?v ?rho } suffix :>> ?k ] |
! { MakeEffect ?a ?b ?x ?k ?tau } ;

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


CHR: conflicting-makes @ { MakeEffect __ __ __ __ __ } { MakeEffect __ __ __ __ __ } // -- | [ "recursive-make" throw f ] ;

CHR: must-cleanup @ { MakeEffect __ __ __ __ __ } <={ body-pred } // -- | [ "leftovers" throw f ] ;

CHR: invalid-stays-invalid @ { Invalid } // { Invalid } -- | ;

CHR: finish-invalid-effect @ // { MakeEffect __ __ __ __ ?tau } { Invalid } -- |
[ ?tau null ==! ] ;

CHR: finish-effect @ // { MakeEffect ?a ?b __ ?l ?tau } -- |
[ ?tau P{ Effect ?a ?b ?l } ==! ] ;

;


: qt ( quot -- res )
    ?TypeOf boa 1array chr-comp swap [ run-chr-query store>> ] with-var-names ;
