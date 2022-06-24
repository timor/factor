USING: accessors arrays assocs chr chr.factor chr.parser chr.state classes
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
! Placeholder-effect?
TUPLE: RecursiveEffect < chr-pred tag effect ;
TUPLE: TypeOf < chr-pred thing type ;
TUPLE: TypeOfWord < chr-pred word var ;
TUPLE: ?TypeOf < chr-pred thing ;


TUPLE: MakeSingleDispatch < chr-pred index cases target ;

! States that q3 is the composition of q1 and q2
TUPLE: ComposeType < chr-pred q1 q2 q3 ;

! Actually triggers computing composed effect and storing it into target
TUPLE: ComposeEffect < chr-pred e1 e2 target ;
TUPLE: MakeEffect < chr-pred in out locals preds target ;
TUPLE: MakeUnit < chr-pred val target ;
TUPLE: Instance < chr-pred id type ;
! For destructuring
TUPLE: Label < chr-pred stack label ;
TUPLE: Literal < chr-pred val ;
TUPLE: Slot < chr-pred obj n val ;
TUPLE: Declare < chr-pred classes stack ;

TUPLE: CallEffect < chr-pred thing in out ;
TUPLE: CallRecursive < chr-pred tag ;

TUPLE: Recursive < chr-pred tag effect ;
TUPLE: Loop < chr-pred tag in out ;
TUPLE: Continue < chr-pred tag ;
TUPLE: Recursion < chr-pred tag from to ;
TUPLE: MakeXor < chr-pred type1 type2 target ;
TUPLE: MakeRecursion < chr-pred type target ;

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
! CHR: same-recursive-type @ { TypeOf ?x ?tau } { RecursiveEffect ?x __ } // { TypeOf ?x ?sig } -- [ ?sig term-var? ] [ ?x callable-word? ] |
! { RecursiveEffect ?x P{ Effect ?a ?b f } }
! [ ?sig P{ Effect ?a ?b f } ==! ] ;

CHR: same-type @ { TypeOf ?x ?tau } // { TypeOf ?x ?sig } -- [ ?tau term-var? not ] | [ ?sig ?tau ==! ] ;
! CHR: same-type @ { TypeOf ?x ?tau } // { TypeOf ?x ?sig } -- | [ ?sig ?tau ==! ] ;

! CHR: same-data-type @ { TypeOf ?x ?tau } // { TypeOf ?x ?sig } -- [ ?x callable-word? not ]
! [ ?tau term-var? ] [ ?sig term-var? ] |
! [ ?tau ?sig ==! ] ;


CHR: double-inference @ { TypeOf ?x ?tau } // { TypeOf ?x ?sig } -- [ ?tau term-var? ] [ ?sig term-var? ] |
{ Recursion ?x ?sig ?tau } ;

! remNOTE: We assume a fixpoint, so this must be a nop...

! CHR: double-inference @ { TypeOf ?x ?tau } // { TypeOf ?x ?sig } -- [ ?sig term-var? ] |

! CHR: double-inference @ { TypeOf ?x ?tau } // { TypeOf ?x ?sig } -- [ ?sig term-var? ] [ ?x callable-word? ] |
! CHR: double-inference @ { TypeOf ?x ?tau } // { TypeOf ?x ?sig } -- [ ?sig term-var? ]
! ! [ ?x callable? ] [ ?x length 1 = ] [ ?x first callable-word? ]
! [ ?x callable-word? ]
! |
! ! { TypeOf ?x P{ Recursive ?l ?tau } }
! ! [ ?sig P{ Effect ?a ?a f } ==! ] ;
! ! { Recursion ?x ?l }
! [ ?sig P{ Effect ?a ?b { P{ CallRecursive ?l } } } ==! ]
! ! { Recursion ?x ?l }
!     ;

! CHR: double-inference @ { TypeOfWord ?x ?tau } // { TypeOfWord ?x ?sig } -- [ ?tau term-var? ] [ ?sig term-var? ] [ ?x callable-word? ]
! |
! [ "rec inf" throw ]


! { RecursiveEffect ?x P{ Effect ?a ?b f } }
! [ ?sig P{ Effect ?a ?b f } ==! ]
! { Recursion ?x ?sig ?tau }
! [ ?sig P{ Continue ?x } ==! ]
! { TypeOf ?x ?tau }


! CHR: double-inference @ { TypeOf [ ?x ] ?tau } // { TypeOf [ ?x ] ?sig } -- [ ?x callable-word? ] [ ?sig term-var? ] |

! CHR: double-inference @ { TypeOf ?x ?tau } // { TypeOf ?x ?sig } -- [ ?sig term-var? ] |
! ! [ ?sig Recursion ==! ] ;
! ! [ ?sig P{ Recursion ?x ?tau } ==! ] ;
! ! [ ?sig { Recursion ?sig } ]
! { Recursive ?x ?tau ?sig } ;
! ! { Invalid } ;
! ! { Recursive ?x ?sig ?tau } ;
! ! [ ?sig P{ Effect ?a ?b { P{ Loop ?x ?a ?b } } } ==! ] ;
! ! [ ?sig P{ Effect ?a ?b { P{ Invalid } } } ==! ] ;
! ! [ "rec inf" throw f ] ;


CHR: alias-type-defined @ { TypeOfWord ?w ?tau } // -- [ ?w word-alias :>> ?q ] |
{ TypeOf ?q ?tau } ;

CHR: type-of-prim-call @ // { TypeOfWord (call) ?tau } -- |
[ ?tau P{ Effect L{ ?q . ?a } ?b { P{ CallEffect ?q ?a ?b } } } ==! ] ;
! [ ?tau P{ Effect L{ ?q . ?a } ?b { P{ Instance ?q P{ Effect ?a ?b f } } } } ==! ] ;

CHR: type-of-dip @ // { TypeOfWord dip ?tau } -- |
[ ?tau P{ Effect L{ ?q ?x . ?a } L{ ?x . ?b } { P{ CallEffect ?q ?a ?b } } } ==! ] ;
! [ ?tau P{ Effect L{ ?q ?x . ?a } L{ ?x . ?b } { P{ Instance ?q P{ Effect ?a ?b f } } } } ==! ] ;

! CHR: type-of-dup @ // { TypeOf [ dup ] ?tau } -- |
CHR: type-of-dup @ // { TypeOfWord dup ?tau } -- |
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

CHR: type-of-swap @ // { TypeOfWord swap ?tau } -- |
[ ?tau P{ Effect L{ ?x ?y . ?a } L{ ?y ?x . ?a } f } ==! ] ;

CHR: type-of-mux @ // { TypeOfWord ? ?tau } -- |
[
    ?tau
    P{ Xor
       P{ Effect L{ ?q ?p ?c . ?a } L{ ?p . ?a } { P{ Instance ?c not{ W{ f } } } { Drop ?q } { Use ?c } } }
       P{ Effect L{ ?q ?p ?c . ?a } L{ ?q . ?a } { P{ Instance ?c W{ f } } { Drop ?p } { Use ?c } } }
     }
    ==!
] ;

CHR: type-of-predicate @ // { TypeOfWord ?w ?tau } -- [ ?w "predicating" word-prop :>> ?c ] |
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
CHR: type-of-slot @ { TypeOfWord slot ?tau } // -- |
[ ?tau
  P{ Effect L{ ?m ?o . ?a } L{ ?v . ?a } {
         P{ Instance ?m integer }
         P{ Instance ?o union{ tuple array } }
         P{ Slot ?o ?m ?v }
         P{ Use ?m }
         P{ Use ?o }
     } }
  ==! ] ;

UNION: valid-effect-type Effect Xor ;
CHR: have-type-of-word-call @ { TypeOf [ ?w ] ?tau } { TypeOfWord ?w ?sig } // -- [ ?sig valid-effect-type? ] |
[ ?tau ?sig ==! ] ;


! remNOTE: interjecting here in case we get recursion
CHR: type-of-word-call @ { TypeOf [ ?w ] ?tau } // -- [ ?w callable-word? ] [ ?tau term-var? ] |
{ TypeOfWord ?w ?sig }
! CHR: type-of-word-call @ // { TypeOf [ ?w ] ?tau } -- [ ?w callable-word? ] [ ?tau term-var? ] |
! { TypeOf ?w ?rho }
! { ComposeType P{ Effect ?a ?a f } ?rho ?tau } ;
! { TypeOf ?w ?sig } ;
! { TypeOf ?w ?tau }
! { TypeOf [ ?w ] ?tau }
    ;

! ! NOTE interjecting here to catch recursion
! CHR: type-of-callable-unit @ { TypeOf [ ?w ] ?tau } // -- [ ?w callable? ] |
! { TypeOf ?w ?rho }
! { ComposeType P{ Effect ?a ?a f } ?rho ?sig }
! { MakeEffect ?a L{ ?x . ?a } f { P{ Instance ?x ?sig } P{ Literal ?x } } ?tau }
!     ;

CHR: type-of-unit-val @ { TypeOf [ ?v ] ?tau } // -- [ ?v callable-word? not ]
|
{ TypeOf ?v ?rho }
{ MakeUnit ?rho ?tau } ;
! CHR: type-of-unit-val-direct @ { TypeOf [ ?v ] ?tau } // -- [ ?v callable-word? not ]
! |
! { TypeOf ?v ?rho }
! [ ?tau P{ Effect ?a L{ ?x . ?a } { P{ Instance ?x ?rho } } } ==! ]
!     ;

UNION: valid-type Effect classoid ;
GENERIC: free-effect-vars ( term -- term )

CHR: make-unit-type @ // { MakeUnit ?rho ?tau } -- [ { ?rho } first valid-type? ] |
{ MakeEffect ?a L{ ?x . ?a } f { P{ Instance ?x ?rho } P{ Literal ?x } } ?tau } ;

! CHR: push-recursion-xor-unit-type @ // { MakeUnit P{ Recursion P{ Xor ?x ?y } } ?tau } -- |
! { MakeUnit P{ Recursion ?x } ?rho }
! { MakeUnit P{ Recursion ?y } ?sig }
! { MakeXor ?rho ?sig ?tau } ;


! CHR: make-unit-recursive-type @ // { MakeUnit P{ Recursion ?sig } ?tau } -- [ ?sig valid-type? ] |
! [ ?tau P{ Effect ?a L{ ?x . ?a } { P{ Instance ?x P{ Recursion ?sig } } P{ Literal ?x } } } ==! ] ;


! CHR: resolve-unit-recursion @ // { MakeUnit P{ Recursion ?e } ?tau } -- [ ?e term-var? not ] |
! [ ?tau ?e ==! ] ;

CHR: type-of-val @ // { TypeOf A{ ?v } ?tau } -- [ ?v callable? not ] [ ?v callable-word? not ]
|
! { Instance ?tau W{ ?v } } ;
[ ?tau W{ W{ ?v } } ==! ] ;

CHR: type-of-declare @ // { TypeOfWord declare ?tau } -- |
[ ?tau
  P{ Effect L{ ?l . ?a } ?a {
         P{ Instance ?l array }
         P{ Declare ?l ?a }
         P{ Use ?l }
     } }
  ==! ] ;

CHR: type-of-fixnum+ @ { TypeOfWord fixnum+ ?tau } // -- |
[ ?tau
  P{ Effect L{ ?x ?y . ?a } L{ ?z . ?b } { P{ Instance ?x fixnum } P{ Instance ?y fixnum } P{ Use ?x } P{ Use ?y } P{ Instance ?z integer } } }
  ==!
] ;

! *** Other words

! NOTE: initializing effect here because of possibly recursive defs
CHR: type-of-word @ { TypeOfWord A{ ?w } ?tau } // -- [ ?tau term-var? ] [ ?w word-alias not ] [ ?w method? not ] [ ?w callable-word? ] [ ?w "predicating" word-prop not ] [ ?w generic? not ] [ ?w def>> :>> ?q ] |
! { TypeOf ?q ?rho }
! { ComposeType P{ Effect ?a ?a { P{ Label ?a ?w } } } ?rho ?tau }
! [ ?tau P{ Effect ?a ?b ?l } ==! ]
{ TypeOf ?q ?tau }
    ;

! NOTE: initializing effect here because of possibly recursive defs
CHR: type-of-generic @ { TypeOfWord ?w ?tau } // -- [ ?tau term-var? ] [ ?w single-generic? ] [ ?w "methods" word-prop sort-methods <reversed> >list :>> ?l ] [ ?w dispatch# :>> ?i ]
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
{ TypeOfWord ?m ?rho }
{ MakeSingleDispatch ?i ?r ?sig }
{ MakeXor ?rho ?sig ?tau } ;

CHR: type-of-reader @ { TypeOfWord ?w ?tau } // -- [ ?w method? ] [ ?w "reading" word-prop :>> ?x ]
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

CHR: type-of-single-method @ { TypeOfWord ?w ?tau } // -- [ ?w method? ] [ ?w "method-generic" word-prop single-generic? ] [ ?w "reading" word-prop not ]
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

M: Xor free-effect-vars
    [ type1>> ] [ type2>> ] bi [ free-effect-vars ] bi@ append ;
M: Effect free-effect-vars
    preds>> [ free-effect-vars ] gather ;
! M: term-var free-effect-vars 1array ;
M: object free-effect-vars drop f ;
M: Instance free-effect-vars type>> free-effect-vars ;
M: CallRecursive free-effect-vars tag>> 1array ;

: fresh-effect ( effect -- effect )
    dup free-effect-vars fresh-without ;

CHR: compose-effects @ // { ComposeType P{ Effect ?a ?b ?k } P{ Effect ?c ?d ?l } ?tau } --
|
[| |
 P{ Effect ?a ?b ?k } fresh-effect :> e1
 P{ Effect ?c ?d ?l } fresh-effect :> e2
 ! P{ Effect ?a ?b ?k } fresh :> e1
 ! P{ Effect ?c ?d ?l } fresh :> e2
 P{ ComposeEffect e1 e2 ?tau }
] ;

! CHR: compose-null-right @ // { ComposeType ?e null ?tau } -- |
! [ ?tau null ==! ] ;

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
[ ?rho term-var? not ?sig term-var? not or ]
| [ ?tau P{ Xor ?rho ?sig } ==! ] ;

! CHR: compose-break-recursion-left @ // { ComposeType ?sig P{ Recursion __ } ?tau } -- [ ?sig term-var? not ] |
! [ ?tau ?sig ==! ] ;


! CHR: compose-propagate-recursion-left @ // { ComposeType ?sig P{ Recursion ?rho } ?tau } -- [ ?sig term-var? not ] [ ?sig Recursion? not ] [ ?rho term-var? not ] [ break t ] |
! { ComposeType ?sig ?rho ?x }
! { MakeRecursion ?x ?tau } ;

! CHR: did-make-recursion @ // { MakeRecursion ?rho ?tau } -- [ ?rho term-var? not ] [ ?rho Recursion? not ] |
! [ ?tau P{ Recursion ?rho } ==! ] ;

! CHR: did-make-xor-recursion @ // { MakeRecursion ?rho ?tau } -- [ ?rho term-var? not ]

! CHR: lift-xor-recursion @ // { MakeRecursion P{ Xor ?x ?y } }



! CHR: make-xor-recursion @ // { MakeRecursion P{ Xor ?x ?y } ?tau } -- |
! { MakeRecursion ?x ?rho }
! { MakeRecursion ?y ?sig }
! { MakeXor ?rho ?sig ?tau } ;

! CHR: make-xor-recursion @ // { MakeRecursion P{ Xor ?x ?y } ?tau } -- |
! ! { MakeXor ?x ?y ?rho }
! ! { MakeRecursion ?rho ?tau } ;
! { MakeRecursion ?x ?rho }
! { MakeRecursion ?y ?sig } ;
! { MakeXor ?rho ?sig ?tau } ;

! CHR: make-recursion-effect @ // { MakeRecursion P{ Effect ?a ?b ?l } ?tau } -- |
! [ ?tau P{ Recursion P{ Effect ?a ?b ?l } } ==! ] ;


! ** Start Reasoning
UNION: body-pred Instance Label CallEffect Bind Drop Use Literal Declare Slot Loop CallRecursive ;

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

! CHR: same-slot-must-be-same-var @ { Slot ?o ?n ?v } // { Slot ?o ?n ?w } -- | [ ?v ?w ==! ] ;

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

CHR: known-declare @ // { Declare ?l ?a } { Literal ?l } { Instance ?l ?tau } -- |
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

CHR: collect-call-recursive @ // AS: ?e P{ MakeEffect ?a ?b ?x ?l ?tau } AS: ?p P{ CallRecursive ?c } --
[ ?l ?p suffix :>> ?k ]
| { MakeEffect ?a ?b ?x ?k ?tau } ;

CHR: collect-body-pred @ // AS: ?e P{ MakeEffect ?a ?b ?x ?l ?tau } AS: ?p <={ body-pred } -- [ ?p vars ?e effect-vars subset? ]
[ ?l ?p suffix :>> ?k ]
|
{ MakeEffect ?a ?b ?x ?k ?tau } ;

CHR: collect-slot-defs @ // AS: ?e P{ MakeEffect ?a ?b ?x ?l ?tau } AS: ?p P{ Slot ?o ?n ?v } --
[ ?o ?e effect-vars in? ]
[ ?l ?p suffix :>> ?k ]
[ ?x ?n vars union ?v vars union :>> ?y ] |
{ MakeEffect ?a ?b ?y ?k ?tau } ;

! This will catch [ [ some-generic-word ] call ] inferences
! CHR: catch-xor-effect @ // { MakeEffect ?a ?b f f ?tau } { Literal ?q } { Instance ?q P{ Xor ?x ?y } } { CallEffect ?q ?a ?b } --
! [ ?a term-var? ] [ ?b term-var? ] |
! [ ?tau P{ Xor ?x ?y } ==! ] ;

CHR: catch-unit-effect-call @ // { MakeEffect ?a ?b f f ?tau } { Literal ?q } { Instance ?q ?rho } { CallEffect ?q ?a ?b } --
[ ?rho term-var? not ]
[ ?a term-var? ] [ ?b term-var? ] |
[ ?tau ?rho ==! ] ;

CHR: conflicting-makes @ { MakeEffect __ __ __ __ __ } { MakeEffect __ __ __ __ __ } // -- | [ "recursive-make" throw f ] ;

CHR: must-cleanup @ { MakeEffect __ __ __ __ __ } AS: ?p <={ body-pred } // -- | [ ?p "leftovers" 2array throw f ] ;

CHR: invalid-stays-invalid @ { Invalid } // { Invalid } -- | ;

CHR: finish-invalid-effect @ // { MakeEffect __ __ __ __ ?tau } { Invalid } -- |
[ ?tau null ==! ] ;

CHR: finish-effect @ // { MakeEffect ?a ?b __ ?l ?tau } -- |
[ ?tau P{ Effect ?a ?b ?l } ==! ] ;

! *** Recursion resolution

! Resolve Continuations composing recursive effects
CHR: resolve-recursive-right @ { ComposeType ?x ?sig ?rho } { ComposeType ?y ?rho ?d } // { Recursion ?l ?sig ?e } --
[ ?e valid-effect-type? ] [ ?x valid-effect-type? ] [ ?y valid-effect-type? ] |
[ ?sig P{ Effect ?a ?b { P{ CallRecursive ?l } } } ==! ] ;


! ! ! TODO: late enough?
! ! CHR: copy-recursive-right @ // { ComposeType ?e P{ Recursion __ } ?tau } -- |
! ! [ ?tau ?e ==! ] ;

! CHR: resolve-recursive-right @ // { Recursive __ ?tau ?sig } -- [ ?sig term-var? not ] [ ?tau term-var? ] |
! [ ?tau ?sig ==! ] ;

! CHR: resolve-recursive-left @ // { Recursive __ ?tau ?sig } -- [ ?tau term-var? not ] [ ?sig term-var? ] |
! [ ?sig ?tau ==! ] ;

! CHR: same-recursion @ { Recursion ?x ?a } // { Recursion ?x ?b } -- | [ ?a ?b ==! ] ;
! CHR: same-recursion @ { TypeOf ?x P{ Recursive ?l ?tau } } // { Recursion ?x ?b } -- | [ ?b ?l ==! ] ;

! CHR: wrap-recursion @ // { Recursion ?x ?l } { TypeOf ?x ?tau } -- | { TypeOf ?x P{ Recursive ?l ?tau } } ;




;


: qt ( quot -- res )
    ?TypeOf boa 1array chr-comp swap [ run-chr-query store>> ] with-var-names ;
