USING: accessors arrays assocs chr chr.factor chr.parser chr.state
classes.algebra classes.tuple combinators combinators.short-circuit effects
generic generic.single kernel kernel.private lists math math.parser math.private
quotations sequences sets slots.private strings terms types.util words
words.symbol ;

IN: chr.factor.composition

PREDICATE: callable-word < word { [ symbol? not ] } 1&& ;

! * Helpers for generating declared effects

GENERIC: elt>var ( i elt -- obj )
M: f elt>var drop number>string "v" prepend utermvar ;
M: string elt>var nip utermvar ;
M: pair elt>var
    first2 drop elt>var ;

: elt-vars ( seq -- seq )
    [ swap elt>var ] map-index ;
: effect>stack-elts ( effect -- lin lout )
    [ in>> elt-vars <reversed> >list ]
    [ out>> elt-vars <reversed> >list ] bi ;

:: add-row-vars ( lin lout effect -- lin lout )
    effect [ in-var>> ] [ out-var>> ] bi
    [ dup [ utermvar ] when ] bi@
    :> ( i o )
    { { [ i o [ not ] both? ]
        [ "rho" utermvar :> rho
          lin rho list*
          lout rho list* ] }
      { [ i o [  ] both? ]
        [ lin i list*
          lout o list* ] }
      [ lin __ list* lout __ list* ]
    } cond ;

: effect>stacks ( effect -- lin lout )
    [ effect>stack-elts ]
    [ add-row-vars ] bi ;

! * Compositional approach

TUPLE: Eval < chr-pred code stack ;
TUPLE: Effect < chr-pred in out preds ;
TUPLE: TypeOf < chr-pred thing type ;
TUPLE: ?TypeOf < chr-pred thing ;


TUPLE: MakeSingleDispatch < chr-pred index cases target ;

! States that q3 is the composition of q1 and q2
TUPLE: ComposeType < chr-pred q1 q2 q3 ;

! Actually triggers computing composed effect and storing it into target
TUPLE: ComposeEffect < chr-pred e1 e2 target ;
TUPLE: MakeEffect < chr-pred in out locals preds target ;
TUPLE: Instance < chr-pred id type ;
! For destructuring
TUPLE: Label < chr-pred stack label ;
TUPLE: Literal < chr-pred val ;
TUPLE: Slot < chr-pred obj n val ;
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
TUPLE: Gt < chr-pred val1 val2 ;


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
! ** Type Definitions
CHR: start-type-of @ // { ?TypeOf ?q } -- | { TypeOf ?q ?tau } ;

CHR: unique-type @ { TypeOf ?x ?tau } // { TypeOf ?x ?tau } -- | ;
CHR: same-type @ { TypeOf ?x ?tau } // { TypeOf ?x ?sig } -- | [ ?tau ?sig ==! ] ;


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

! : slot ( obj m -- value )
CHR: type-of-slot @ { TypeOf slot ?tau } // -- |
[ ?tau
  P{ Effect L{ ?m ?o . ?a } L{ ?v . ?a } {
         P{ Instance ?m integer }
         P{ Instance ?o union{ tuple array } }
         P{ Slot ?o ?m ?v }
         P{ Use ?m }
         P{ Use ?o }
     } }
  ==! ] ;

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

CHR: type-of-fixnum+ @ { TypeOf fixnum+ ?tau } // -- |
[ ?tau
  P{ Effect L{ ?x ?y . ?a } L{ ?z . ?b } { P{ Instance ?x fixnum } P{ Instance ?y fixnum } P{ Use ?x } P{ Use ?y } P{ Instance ?z integer } } }
  ==!
] ;

! *** Other words

! NOTE: initializing effect here because of possibly recursive defs
CHR: type-of-word @ { TypeOf A{ ?w } ?tau } // -- [ ?w word-alias not ] [ ?w method? not ] [ ?w callable-word? ] [ ?w "predicating" word-prop not ] [ ?w generic? not ] [ ?w def>> :>> ?q ] |
! { TypeOf ?q ?rho }
! { ComposeType P{ Effect ?a ?a { P{ Label ?a ?w } } } ?rho ?tau }
[ ?tau P{ Effect ?a ?b ?l } ==! ]
{ TypeOf ?q ?tau }
    ;

! NOTE: initializing effect here because of possibly recursive defs
CHR: type-of-generic @ { TypeOf ?w ?tau } // -- [ ?w single-generic? ] [ ?w "methods" word-prop sort-methods <reversed> >list :>> ?l ] [ ?w dispatch# :>> ?i ]
[ ?w stack-effect effect>stacks :>> ?b drop :>> ?a ]
|
! [ ?tau P{ Effect ?a ?b ?k } ==! ]
{ MakeSingleDispatch ?i ?l ?tau } ;

: dispatch-decl ( class num -- seq )
    dup 1 + object <array> [ set-nth ] keep ;

CHR: dispatch-done @ // { MakeSingleDispatch __ +nil+ ?tau } -- | [ ?tau null ==! ] ;
CHR: dispatch-case @ // { MakeSingleDispatch ?i L{ { ?c ?m } . ?r } ?tau } --
! [ ?c ?i dispatch-decl :>> ?l ]
! [ [ ?l declare ] ?m def>> compose :>> ?q ]
|
! { TypeOf ?q ?rho }
{ TypeOf ?m ?rho }
{ MakeSingleDispatch ?i ?r ?sig }
{ MakeXor ?rho ?sig ?tau } ;

CHR: type-of-reader @ { TypeOf ?w ?tau } // -- [ ?w method? ] [ ?w "reading" word-prop :>> ?x ]
[ ?w "method-class" word-prop :>> ?c ]
[ ?x class>> :>> ?d ] [ ?x name>> :>> ?n ] |
[ ?tau
  P{ Effect L{ ?o . ?a } L{ ?v . ?a }
     {
         P{ Instance ?o ?c }
         P{ Slot ?o ?n ?v }
         P{ Instance ?v ?d }
         P{ Use ?o }
     }
   }
  ==! ] ;

CHR: type-of-single-method @ { TypeOf ?w ?tau } // -- [ ?w method? ] [ ?w "method-generic" word-prop single-generic? ] [ ?w "reading" word-prop not ]
[ ?w def>> :>> ?q ]
[ ?w "method-class" word-prop
  ?w "method-generic" word-prop dispatch#
  dispatch-decl <reversed> >list :>> ?l
]
|
{ TypeOf ?q ?rho }
{ ComposeType P{ Effect ?a ?a { P{ Declare ?l ?a } } } ?rho ?tau } ;


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

CHR: compose-xor-effects-right @ // { ComposeType P{ Effect ?a ?b ?k } P{ Xor ?x ?y } ?tau } -- |
{ ComposeType P{ Effect ?a ?b ?k } ?x ?rho }
{ ComposeType P{ Effect ?a ?b ?k } ?y ?sig }
{ MakeXor ?rho ?sig ?tau } ;

CHR: compose-xor-effects-left @ // { ComposeType P{ Xor ?x ?y } P{ Effect ?a ?b ?k } ?tau } -- |
{ ComposeType ?x P{ Effect ?a ?b ?k } ?rho }
{ ComposeType ?y P{ Effect ?a ?b ?k } ?sig }
{ MakeXor ?rho ?sig ?tau } ;


CHR: compose-xor-effects-both @ // { ComposeType P{ Xor ?a ?b } P{ Xor ?c ?d } ?tau } -- |
{ ComposeType ?a P{ Xor ?c ?d } ?rho }
{ ComposeType ?b P{ Xor ?c ?d } ?sig }
{ MakeXor ?rho ?sig ?tau }
! [ ?tau P{ Xor ?rho ?sig } ==! ]
    ;


CHR: make-null-xor @ // { MakeXor null null ?tau } -- | [ ?tau null ==! ] ;
CHR: make-trivial-xor-left @ // { MakeXor ?rho null ?tau } -- | [ ?rho ?tau ==! ] ;
CHR: make-trivial-xor-right @ // { MakeXor null ?rho ?tau } -- | [ ?rho ?tau ==! ] ;
! NOTE: not closing until we have effect!
! NOTE: but that is not good if we need this to exclude stuff!
CHR: make-xor @ // { MakeXor ?rho ?sig ?tau } --
! [ ?rho term-var? not ] [ ?sig term-var? not ]
| [ ?tau P{ Xor ?rho ?sig } ==! ] ;

! ** Start Reasoning
UNION: body-pred Instance Label CallEffect Bind Drop Use Literal Declare Slot ;

! NOTE: assumed renaming here already
CHR: rebuild-compose-effect @ // { ComposeEffect P{ Effect ?a ?b ?k } P{ Effect ?c ?d ?l } ?tau } -- |
[ ?b ?c ==! ]
! NOTE: This happens if we have pre-defined effects but no known body yet (e.g. recursive calls)
[ ?k dup term-var? [ drop f ] when ]
[ ?l dup term-var? [ drop f ] when ]
{ MakeEffect ?a ?d f f ?tau } ;

! ** Simplification/Intra-Effect reasoning
CHR: early-exit @ { Invalid } // <={ body-pred } -- | ;

CHR: unique-instance @ { Instance ?x ?tau } // { Instance ?x ?tau } -- | ;

CHR: uniqe-slot @ { Slot ?o ?n ?v } // { Slot ?o ?n ?v } -- | ;

CHR: same-slot-must-be-same-var @ { Slot ?o ?n ?v } // { Slot ?o ?n ?w } -- | [ ?v ?w ==! ] ;

CHR: useless-instance @ // { Instance __ object } -- | ;

CHR: instance-intersection @ // { Instance ?x A{ ?tau } } { Instance ?x A{ ?sig } } -- [ { ?tau ?sig } first2 class-and :>> ?c ] |
{ Instance ?x ?c } ;

CHR: null-instance-is-invalid @ { Instance __ null } // -- | { Invalid } ;

! *** Bind simplifaction

CHR: unique-bind-is-same @ // { Bind ?x { ?y } } -- | [ ?x ?y ==! ] ;

CHR: central-bind-point @ // { Bind ?x ?l } { Bind ?a ?k } -- [ ?a ?l in? ]
[ ?a ?l remove ?k union :>> ?m ] |
{ Bind ?x ?m } ;

CHR: drop-cancels-bind @ // { Drop ?x } { Bind ?a ?l } -- [ ?x ?l in? ]
[ ?x ?l remove :>> ?k ] |
{ Bind ?a ?k } ;

CHR: drop-cancels-lit @ // { Drop ?x } { Instance ?x __ } { Literal ?x } -- | ;

! *** Bind propagation

CHR: bind-propagates-literals @ // { Bind ?x ?l } { Literal ?x } { Instance ?x ?tau } -- [ { ?tau } first :>> ?c ] |
[ ?l [ { ?c } first fresh Instance boa ] map ]
[ ?l [ Literal boa ] map ] ;

CHR: bind-propagates-instance @ { Bind ?x ?l } { Instance ?x ?tau } // -- [ { ?tau } first :>> ?c ] |
[ ?l [ { ?c } first fresh Instance boa ] map ] ;

CHR: bind-backprops-instance @ { Bind ?x ?l } { Instance ?v ?tau } // -- [ ?v ?l in? ] [ { ?tau } first :>> ?c ] |
{ Instance ?x ?tau } ;

CHR: bind-backprops-slot @ { Bind ?x ?l } { Slot ?o ?n ?v } // -- [ ?o ?l in? ] |
{ Slot ?x ?n ?v } ;

CHR: used-propagated-instance @ { Use ?x } { Bind __ ?l } // { Instance ?x __ } -- [ ?x ?l in? ] | ;
CHR: use-propagated-slot @ { Use ?o } { Bind __ ?l } // { Slot ?o __ __ } -- [ ?o ?l in? ] | ;

CHR: use-cancels-bind @ // { Use ?x } { Bind ?a ?l } -- [ ?x ?l in? ]
[ ?x ?l remove :>> ?k ] |
{ Bind ?a ?k } ;

! CHR: same-lit-is-same-var @ { Literal ?x } { Instance ?x A{ ?v } } // { Literal ?y } { Instance ?y A{ ?v } } -- |
! [ ?x ?y ==! ] ;

! *** Call Effect matching
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

! *** Substituting ground values into body constraints

CHR: known-declare @ { Declare ?l ?a } { Literal ?l } { Instance ?l ?tau } // -- |
[ ?l ?tau <reversed> >list ==! ] ;

CHR: known-slot @ { Literal ?n } { Instance ?n ?tau } // { Slot ?o ?n ?v } -- |
{ Slot ?o ?tau ?v } ;

! Slot conversion
CHR: known-named-slot @ { Instance ?o A{ ?tau } } // { Slot ?o A{ ?n } ?v } -- [ ?tau tuple-class? ]
[ ?tau all-slots [ offset>> ?n = ] find nip :>> ?s ] [ ?s name>> :>> ?m ]
[ ?s class>> :>> ?rho ]
|
{ Slot ?o ?m ?v }
{ Instance ?v ?rho }
    ;


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

! This will catch [ [ some-generic-word ] call ] inferences
CHR: make-xor-effect @ // { MakeEffect ?a ?b ?x ?l ?tau } { Literal ?q } { Instance ?q P{ Xor P{ Effect ?c ?d ?k } P{ Effect ?rho ?sig ?m } } } { CallEffect ?q ?a ?b } --
[ ?a term-var? ] [ ?b term-var? ] |
[ ?tau P{ Xor P{ Effect ?c ?d ?k } P{ Effect ?rho ?sig ?m } } ==! ] ;


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
