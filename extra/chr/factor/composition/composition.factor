USING: accessors arrays assocs chr chr.factor chr.parser chr.state classes
classes.algebra classes.tuple classes.tuple.private combinators
combinators.short-circuit effects generic generic.single kernel kernel.private
lists macros math math.parser math.private quotations sequences sets
slots.private sorting strings terms types.util words words.symbol ;

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
TUPLE: ?TypeOf < chr-pred thing type ;
TUPLE: TypeOfWord < chr-pred word var ;
TUPLE: InferType < chr-pred thing ;
TUPLE: WaitFull < chr-pred type ;
TUPLE: WaitRec < chr-pred orig rec ;
TUPLE: Throws < chr-pred error ;

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
TUPLE: MacroCallEffect < chr-pred word in out ;
TUPLE: CallRecursive < chr-pred tag in out ;

TUPLE: Boa < chr-pred spec in id ;
TUPLE: TupleBoa < Boa ;

! Macro expansion, folding
TUPLE: FoldStack < chr-pred stack n ;
TUPLE: FoldCall < chr-pred stack n quot target ;

! TUPLE: Recursive < chr-pred tag effect ;
TUPLE: Recursive < chr-pred tag ;
TUPLE: Loop < chr-pred tag in out ;
TUPLE: Continue < chr-pred tag ;
TUPLE: Recursion < chr-pred tag from to ;
TUPLE: MakeXor < chr-pred type1 type2 target ;
TUPLE: MakeRecursion < chr-pred type target ;
TUPLE: MakeFoldable < chr-pred type target ;
TUPLE: Copy < chr-pred type target ;

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
        { if [ ? call ] }
        { loop [ [ call ] keep swap [ loop ] [ drop ] if ] }
    } at ;

CHRAT: chr-comp { TypeOf }


! Tag-level concrete type!
! ** Type Definitions
CHR: start-type-of @ // { InferType ?q } -- | { ?TypeOf ?q ?tau } ;

CHR: unique-type @ { TypeOf ?x ?tau } // { TypeOf ?x ?tau } -- | ;

GENERIC: free-effect-vars ( term -- term )
: full-type? ( type -- ? ) free-effect-vars empty? ;

CHR: conflicting-type @ { TypeOf ?x ?tau } // { TypeOf ?x ?sig } -- [ ?tau full-type? ] [ ?sig full-type? ] | [ "conflicting type-defs" throw f ] ;

CHR: done-with-intermediate-types @ // { ?TypeOf ?x +nil+ } -- | ;
CHR: answer-intermediate-type @ // { ?TypeOf ?x L{ ?tau . ?r } } { TypeOf ?x ?sig } -- |
! TODO: order matters?
{ ?TypeOf ?x ?r }
[ ?tau ?sig ==! ]
    ;

CHR: answer-type @ { TypeOf ?x ?tau } // { ?TypeOf ?x ?sig } -- [ ?tau term-var? not ] | [ ?sig ?tau ==! ] ;

TUPLE: PushdownRec < chr-pred label val type ;

! CHR: double-word-inference @ { TypeOfWord ?x ?tau } // { TypeOfWord ?x ?sig } -- [ ?tau term-var? ] [ ?sig term-var? ] |
CHR: double-word-inference @ { ?TypeOf [ ?x ] ?tau } // { ?TypeOf [ ?x ] ?sig } -- [ ?tau term-var? ] [ ?sig term-var? ]
[ ?x callable-word? ]
! [ ?x 1quotation :>> ?y ]
|
! [ ?sig P{ Recursive ?x ?tau } ==! ] ;
! { Recursion ?y ?sig ?tau }
! { PushdownRec ?y ?sig } ;
{ Recursion ?x ?sig ?tau } ;
! { PushdownRec ?x ?sig ?tau } ;

CHR: double-inference-queue @ { ?TypeOf ?x ?tau } // { ?TypeOf ?x ?sig } -- [ ?tau term-var? ] [ ?sig term-var? ] |
! [ ?sig P{ Recursive ?x ?tau } ==! ]  ;
{ Recursion ?x ?sig ?tau } ;
! { PushdownRec ?x ?sig ?tau } ;
! { ?TypeOf ?x L{ ?sig } } ;

CHR: alias-type-defined @ { TypeOfWord ?w ?tau } // -- [ ?w word-alias :>> ?q ] |
{ ?TypeOf ?q ?tau } ;

CHR: type-of-prim-call @ // { ?TypeOf [ (call) ] ?tau } -- |
[ ?tau P{ Effect L{ ?q . ?a } ?b { P{ CallEffect ?q ?a ?b } } } ==! ] ;

CHR: type-of-dip @ { TypeOfWord dip ?tau } // -- |
[ ?tau P{ Effect L{ ?q ?x . ?a } L{ ?x . ?b } { P{ CallEffect ?q ?a ?b } } } ==! ] ;

CHR: type-of-dup @ { TypeOfWord dup ?tau } // -- |
[ ?tau P{ Effect L{ ?x . ?rho } L{ ?y ?z . ?rho } {
              P{ Bind ?x { ?y ?z } }
          } }
  ==! ] ;

CHR: type-of-drop @ // { ?TypeOf [ drop ] ?tau } -- |
[ ?tau P{ Effect L{ ?x . ?a } ?a { P{ Drop ?x } } } ==! ] ;

CHR: type-of-swap @ // { ?TypeOf [ swap ] ?tau } -- |
[ ?tau P{ Effect L{ ?x ?y . ?a } L{ ?y ?x . ?a } f } ==! ] ;

CHR: type-of-mux @ // { ?TypeOf [ ? ] ?tau } -- |
[
    ?tau
    P{ Xor
       P{ Effect L{ ?q ?p ?c . ?a } L{ ?p . ?a } { P{ Instance ?c not{ W{ f } } } { Drop ?q } { Use ?c } } }
       P{ Effect L{ ?q ?p ?c . ?a } L{ ?q . ?a } { P{ Instance ?c W{ f } } { Drop ?p } { Use ?c } } }
     }
    ==!
] ;

CHR: type-of-predicate @ { TypeOfWord ?w ?tau } // -- [ ?w "predicating" word-prop :>> ?c ] [ ?tau term-var? ] |
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
CHR: type-of-slot @ { TypeOfWord slot ?tau } // -- [ ?tau term-var? ] |
[ ?tau
  P{ Effect L{ ?m ?o . ?a } L{ ?v . ?a } {
         P{ Instance ?m integer }
         P{ Instance ?o union{ tuple array } }
         P{ Slot ?o ?m ?v }
         P{ Use ?m }
         P{ Use ?o }
     } }
  ==! ] ;


CHR: type-of-throw @ // { ?TypeOf [ throw ] ?tau } -- |
! [ ?tau P{ Effect ?a +bottom+ f } ==! ] ;
! [ ?tau null ==! ] ;
[ ?tau P{ Effect L{ ?e . ?a } L{ ?e . ?a } {
              P{ Throws ?e }
              P{ Use ?e }
              ! P{ Invalid }
          } }
  ==! ] ;

CHR: type-of-boa @ // { ?TypeOf [ boa ] ?tau } -- |
[ ?tau
  P{ Effect L{ ?c . ?a } L{ ?v . ?b } { P{ Instance ?c tuple-class } P{ Boa ?c ?a L{ ?v . ?b } }
                                        P{ Use ?c }
                                        P{ Instance ?v tuple } } }
  ==!
] ;

CHR: type-of-tuple-boa @ // { ?TypeOf [ <tuple-boa> ] ?tau } -- |
[ ?tau
  P{ Effect L{ ?c . ?a } L{ ?v . ?b } { P{ Instance ?c array } P{ TupleBoa ?c ?a L{ ?v . ?b } }
                                        P{ Use ?c }
                                        P{ Instance ?v tuple } } }
  ==!
] ;


! *** Destructure unit type queries
UNION: valid-effect-type Effect Xor ;
UNION: valid-type Effect classoid ;

TUPLE: MaybeHaveFold < chr-pred word quot type target ;

CHR: have-type-of-word-call @ { ?TypeOf [ ?w ] ?sig } { TypeOfWord ?w ?rho } // --
[ ?rho valid-effect-type? ]
[ ?w 1quotation :>> ?q ]
|
! [ ?sig ?rho ==! ]
{ TypeOf ?q ?rho } ;

CHR: type-of-wrapper @ // { ?TypeOf ?q ?tau } --
[ ?q quotation? ]
[ ?q length 1 = ]
[ ?q first wrapper? ]
[ ?q first :>> ?v ]
|
[
    ?tau
    P{ Effect ?a L{ ?x . ?a } { P{ Instance ?x ?v } P{ Literal ?x } } }
    ==!
] ;


CHR: ask-type-of-word-call @ { ?TypeOf [ ?w ] ?tau } // -- [ ?w callable-word? ] [ ?tau term-var? ] |
{ TypeOfWord ?w ?sig } ;

CHR: type-of-unit-val @ { ?TypeOf [ ?v ] ?tau } // -- [ ?v callable-word? not ]
[ ?v 1quotation :>> ?q ] |
{ ?TypeOf ?v ?rho }
{ MakeUnit ?rho ?sig }
{ TypeOf ?q ?sig }
    ;

CHR: make-simple-unit-type @ // { MakeUnit ?rho ?tau } -- [ { ?rho } first valid-type? ] |
[ ?tau P{ Effect ?a L{ ?x . ?a } { P{ Instance ?x ?rho } P{ Literal ?x } } } ==! ] ;

CHR: make-xor-unit-type @ // { MakeUnit P{ Xor ?x ?y } ?tau } -- |
{ MakeXor ?rho ?sig ?tau }
{ MakeUnit ?x ?rho }
{ MakeUnit ?y ?sig } ;

CHR: type-of-val @ // { ?TypeOf A{ ?v } ?tau } -- [ ?v callable? not ] [ ?v callable-word? not ]
|
[ ?tau W{ W{ ?v } } ==! ] ;

CHR: type-of-declare @ { TypeOfWord declare ?tau } // -- |
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

! *** Typed words
CHR: type-of-typed-word @ { TypeOfWord A{ ?w } ?tau } // --
[ ?tau term-var? ]
[ ?w "typed-def" word-prop :>> ?q ]
[ ?w "declared-effect" word-prop effect-in-types :>> ?a ]
|
{ ?TypeOf ?q ?rho }
{ ComposeType P{ Effect ?x ?x { P{ Declare ?a ?x } } } ?rho ?tau } ;

! *** Other words

CHR: type-of-macro @ { TypeOfWord A{ ?w } ?tau } // --
[ ?tau term-var? ]
[ ?tau macro? ]
[ ?w "transform-quot" word-prop :>> ?q ] |
{ ?TypeOf ?q ?rho }
! { ?TypeOf [ call call ] ?sig }
! { ComposeType ?rho ?sig ?tau }
;

CHR: type-of-word @ { TypeOfWord A{ ?w } ?tau } // --
[ ?tau term-var? ]
[ ?w word-alias not ]
[ ?w method? not ]
[ ?w callable-word? ]
[ ?w "no-compile" word-prop not ]
[ ?w "predicating" word-prop not ]
[ ?w "transform-quot" word-prop not ]
[ ?w generic? not ]
[ ?w def>> :>> ?q ] |
{ ?TypeOf ?q ?tau }
    ;

CHR: type-of-generic @ { TypeOfWord ?w ?tau } // --
[ ?tau term-var? ]
[ ?w single-generic? ]
[ ?w "transform-quot" word-prop not ]
[ ?w "methods" word-prop sort-methods <reversed> >list :>> ?l ]
[ ?w dispatch# :>> ?i ]
[ ?w stack-effect effect>stacks :>> ?b drop :>> ?a ]
|
{ MakeSingleDispatch ?i ?l ?tau } ;

: dispatch-decl ( class num -- seq )
    dup 1 + object <array> [ set-nth ] keep ;

CHR: dispatch-done @ // { MakeSingleDispatch __ +nil+ ?tau } -- | [ ?tau null ==! ] ;
CHR: dispatch-case @ // { MakeSingleDispatch ?i L{ { ?c ?m } . ?r } ?tau } --
|
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
{ ?TypeOf ?q ?rho }
{ ComposeType P{ Effect ?a ?a { P{ Declare ?l ?a } } } ?rho ?tau } ;


CHR: type-of-empty-quot @ // { ?TypeOf [ ] ?tau } -- | [ ?tau P{ Effect ?a ?a f } ==! ] ;

CHR: type-of-quot @ { ?TypeOf ?q ?tau } // -- [ ?q callable? ] [ ?q length 1 > ] [ ?q dup length 2 /i cut :>> ?y drop :>> ?x drop t ] |
{ ?TypeOf ?x ?rho }
{ ?TypeOf ?y ?sig }
{ ComposeType ?rho ?sig ?z }
{ TypeOf ?q ?z } ;

M: Xor free-effect-vars
    [ type1>> ] [ type2>> ] bi [ free-effect-vars ] bi@ append ;
M: Effect free-effect-vars
    preds>> [ free-effect-vars ] gather ;
M: term-var free-effect-vars 1array ;
M: object free-effect-vars drop f ;
M: Instance free-effect-vars type>> free-effect-vars ;
M: CallRecursive free-effect-vars tag>> free-effect-vars ;

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

CHR: compose-null-right @ // { ComposeType ?e null ?tau } -- |
[ ?tau null ==! ] ;

CHR: compose-null-left @ // { ComposeType null ?e ?tau } -- |
[ ?tau null ==! ] ;

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


! NOTE: While kept for reasoning in straight-line composition,
! we don't allow errors into intersection types
CHR: exclude-error-xor-left @ // { MakeXor P{ Effect __ __ ?k } ?sig ?tau } -- [ ?k [ Throws? ] any? ] |
{ MakeXor null ?sig ?tau } ;
CHR: exclude-error-xor-right @ // { MakeXor ?rho P{ Effect __ __ ?k } ?tau } -- [ ?k [ Throws? ] any? ] |
{ MakeXor ?rho null ?tau } ;



CHR: fail-on-rhs-xor @ // { MakeXor __ __ ?tau } -- [ ?tau term-var? not ] |
[ ?tau "not term-var in xor" 2array throw f ] ;
CHR: make-null-xor @ // { MakeXor null null ?tau } -- | [ ?tau null ==! ] ;
CHR: make-trivial-xor-left @ // { MakeXor ?rho null ?tau } -- | [ ?rho ?tau ==! ] ;
CHR: make-trivial-xor-right @ // { MakeXor null ?rho ?tau } -- | [ ?rho ?tau ==! ] ;
CHR: make-xor @ // { MakeXor ?rho ?sig ?tau } --
[ ?rho term-var? not ?sig term-var? not or ]
| [ ?tau P{ Xor ?rho ?sig } ==! ] ;


! ** Start Reasoning
UNION: body-pred Instance Label CallEffect Bind Drop Use Literal Declare Slot Loop CallRecursive Throws ;

! NOTE: assumed renaming here already
CHR: rebuild-compose-effect @ // { ComposeEffect P{ Effect ?a ?b ?k } P{ Effect ?c ?d ?l } ?tau } -- |
[ ?b ?c ==! ]
! NOTE: This happens if we have pre-defined effects but no known body yet (e.g. recursive calls)
! [ ?k dup term-var? [ drop f ] when ]
! [ ?l dup term-var? [ drop f ] when ]
[ ?k ]
[ ?l ]
{ MakeEffect ?a ?d f f ?tau } ;

! ** Simplification/Intra-Effect reasoning

CHR: early-exit @ { Invalid } // <={ body-pred } -- | ;

CHR: unique-instance @ { Instance ?x ?tau } // { Instance ?x ?tau } -- | ;

CHR: uniqe-slot @ { Slot ?o ?n ?v } // { Slot ?o ?n ?v } -- | ;

! NOTE: the reasioning is that this can inductively only happen during composition of two straight-line
! quotation effects. So the instance in the first one is a "provide", and the instance in the second one is an "expect".
! Since the intersection type operation is commutative, we don't care which came from which.
CHR: same-slot-must-be-same-var @ { Slot ?o ?n ?v } // { Slot ?o ?n ?w } -- | [ ?v ?w ==! ] ;

CHR: useless-instance @ // { Instance __ object } -- | ;

CHR: instance-intersection @ // { Instance ?x A{ ?tau } } { Instance ?x A{ ?sig } } -- [ { ?tau ?sig } first2 class-and :>> ?c ] |
{ Instance ?x ?c } ;

CHR: invalid-stays-invalid @ { Invalid } // { Invalid } -- | ;

! CHR: null-instance-is-invalid @ { Instance __ null } // -- | { Invalid } ;
CHR: use-null-instance-is-invalid @ { Use ?x } { Instance ?x null } // -- | { Invalid } ;

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
! NOTE: not sure this has to be restricted to literals, actually, but it feels like we would
! violate the unknown-call safety net...
CHR: call-applies-effect @ // { Literal ?q } { Instance ?q P{ Effect ?c ?d ?l } } { CallEffect ?q ?a ?b } -- |
[ { ?a ?b } { ?c ?d } ==! ]
[ ?l ] ;

! ! This looks really dangerous:
! CHR: call-recursive-applies-literal-effect { Literal ?q } { Instance ?q P{ Effect ?c ?d ?l } } { CallRecursive __ ?a ?b } -- |
! [ { ?a ?b } { ?c ?d } ==! ]
! [ ?l ] ;

CHR: did-declare @ // { Declare +nil+ __ } -- | ;
! NOTE: destructive!
CHR: do-declare @ // { Declare L{ ?tau . ?r } L{ ?x . ?xs } } -- |
{ Instance ?x ?tau }
{ Declare ?r ?xs } ;

! *** Substituting ground values into body constraints

CHR: known-declare @ { Declare ?l ?a } { Literal ?l } { Instance ?l ?tau } // -- |
[ ?l ?tau <reversed> >list ==! ] ;

CHR: constant-declare @ // { Declare ?l ?a } -- [ ?l array? ]
[ ?l <reversed> >list :>> ?m ] |
{ Declare ?m ?a } ;

CHR: known-slot @ { Literal ?n } { Instance ?n ?tau } // { Slot ?o ?n ?v } -- |
{ Slot ?o ?tau ?v } ;

! Slot conversion
CHR: known-named-slot @ { Instance ?o A{ ?tau } } // { Slot ?o A{ ?n } ?v } -- [ ?tau tuple-class? ]
[ ?tau all-slots [ offset>> ?n = ] find nip :>> ?s ] [ ?s name>> :>> ?m ]
[ ?s class>> :>> ?rho ]
|
{ Slot ?o ?m ?v }
{ Instance ?v ?rho } ;

CHR: known-boa-spec @ <={ Boa ?c ?i ?o } { Instance ?c A{ ?v } } { Literal ?c } // -- |
[ ?c ?v ==! ] ;

! *** Boa handling
! NOTE: This is a crucial point regarding re-definitions if we consider incremental operation
CHR: normalize-tuple-boa @ // { Boa A{ ?v } ?i ?o } --
[ ?v tuple-layout :>> ?c ] |
{ TupleBoa ?c ?i ?o } ;

! NOTE: Completely ignoring the hierarchy here
! NOTE: destructive
CHR: tuple-boa-decl @ // { TupleBoa A{ ?c } ?a ?b } --
[ ?c first :>> ?tau ] |
[| |
 ?tau name>> utermvar :> ov
 V{ } clone :> in-vars
 V{ } clone :> preds
 ?tau all-slots [ offset>> ] sort-with
 [| spec i |
     spec name>> :> n
     i n elt>var :> iv
     iv in-vars push
     P{ Slot ov n iv } preds push
     spec class>> :> c
     P{ Instance iv c } preds push
 ] each-index
 in-vars <reversed> >list ?rho lappend :> sin
 P{ Instance ov ?tau } preds push
 L{ ov . ?rho  } :> sout
 [ { ?a ?b } { sin sout } ==! ] preds push
 preds <reversed> >array
] ;

! *** Intra-Effect cleanup

CHR: used-literal @ // { Use ?x } { Literal ?x } { Instance ?x __  } -- | ;
CHR: used-constant @ // { Use A{ ?x } } -- | ;

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

CHR: collect-call-recursive-input @ // AS: ?e P{ MakeEffect ?a ?b ?x ?l ?tau } AS: ?p P{ CallRecursive ?m ?rho ?sig } --
[ ?rho vars ?e effect-vars subset? ]
[ ?x ?sig vars union :>> ?y ]
[ ?l ?p suffix :>> ?k ]
| { MakeEffect ?a ?b ?y ?k ?tau } ;

! CHR: collect-call-recursive @ // AS: ?e P{ MakeEffect ?a ?b ?x ?l ?tau } AS: ?p P{ CallRecursive ?m ?rho ?sig } --
! [ ?rho vars ?sig vars union ?e effect-vars intersects? ]
! [ ?x ?rho vars union ?sig vars union :>> ?y ]
! [ ?l ?p suffix :>> ?k ]
! | { MakeEffect ?a ?b ?y ?k ?tau } ;

CHR: collect-instance @ // AS: ?e P{ MakeEffect ?a ?b ?x ?l ?tau } P{ Instance ?v ?rho } --
[ ?v ?e effect-vars in? ]
[ ?l P{ Instance ?v ?rho } suffix :>> ?k ]
| { MakeEffect ?a ?b ?x ?k ?tau } ;

! CHR: collect-call-recursive @ // AS: ?e P{ MakeEffect ?a ?b ?x ?l ?tau } AS: ?p P{ CallRecursive __ __ __ } --
! [ ?l ?p suffix :>> ?k ]
! | { MakeEffect ?a ?b ?x ?k ?tau } ;

CHR: collect-body-pred @ // AS: ?e P{ MakeEffect ?a ?b ?x ?l ?tau } AS: ?p <={ body-pred } -- [ ?p vars ?e effect-vars subset? ]
[ ?l ?p suffix :>> ?k ]
|
{ MakeEffect ?a ?b ?x ?k ?tau } ;

CHR: collect-slot-defs @ // AS: ?e P{ MakeEffect ?a ?b ?x ?l ?tau } AS: ?p P{ Slot ?o ?n ?v } --
[ ?o ?e effect-vars in? ]
[ ?l ?p suffix :>> ?k ]
[ ?x ?n vars union ?v vars union :>> ?y ] |
{ MakeEffect ?a ?b ?y ?k ?tau } ;

CHR: collect-boa @ // AS: ?e P{ MakeEffect ?a ?b ?x ?l ?tau } AS: ?p <={ Boa ?c ?i ?o } --
! [ ?i ?o [ vars ?e effect-vars in? ] bi@ or ]
[ ?p vars ?e effect-vars intersects? ]
[ ?l ?p suffix :>> ?k ]
[ ?x ?p vars union :>> ?y ] |
{ MakeEffect ?a ?b ?y ?k ?tau } ;

! TODO: abstract this shit...

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

CHR: finish-invalid-effect @ // { MakeEffect __ __ __ __ ?tau } { Invalid } -- |
[ ?tau null ==! ] ;

CHR: finish-effect @ // { MakeEffect ?a ?b __ ?l ?tau } -- |
[ ?tau P{ Effect ?a ?b ?l } ==! ] ;

! *** Recursion resolution


CHR: resolve-have-recursive @ // { Recursion ?l ?rho ?tau } -- [ ?tau full-type? ] |
[ ?rho ?tau ==! ] ;

CHR: compose-call-recursive @ // { ComposeType ?a P{ Recursive ?l } ?tau } --
[ ?a valid-effect-type? ] |
{ ComposeType ?a P{ Effect ?x ?y { P{ CallRecursive ?l ?x ?y } } } ?tau } ;

CHR: make-unit-recursive @ // { MakeUnit P{ Recursive ?l } ?tau } -- |
{ ComposeType P{ Effect ?a ?a f } P{ Recursive ?l } ?sig }
{ MakeUnit ?sig ?tau } ;

! NOTE: renaming the target var in the recursive effect to correctly rebuild the original one...
CHR: resolve-compose-rec-right @ { ComposeType ?a ?tau ?sig } // { Recursion ?l ?x ?e } --
[ ?a valid-effect-type? ]
[ ?tau term-var? ]
[ ?sig term-var? ]
[ ?e valid-effect-type? ]
[ ?sig ?e free-effect-vars in? ] |
[| | ?e { { ?sig ?rho } } lift :> rectype
  P{ Recursion ?l ?x rectype }
]
{ ComposeType ?a P{ Recursive ?l } ?rho }
    ;

! NOTE: In This case we have the target of an unknown composition in the partial type.
CHR: resolve-compose-rec-left @ { ComposeType ?tau ?a ?sig } // { Recursion ?l ?x ?e } --
[ ?a valid-effect-type? ]
[ ?tau term-var? ]
[ ?sig term-var? ]
[ ?e valid-effect-type? ]
[ ?sig ?e free-effect-vars in? ] |
[| | ?e { { ?sig ?rho } } lift :> rectype
 P{ Recursion ?l ?x rectype }
]
[ ?rho
P{ Effect ?i ?o { P{ CallRecursive ?l ?i ?o } } }
==!
]
    ;

! Pull in unknowns
CHR: resolve-xor-rec-tail @ { Recursion ?l __ ?e } //
{ MakeXor ?a ?b ?c } --
[ ?c ?e free-effect-vars in? ] |
[ ?c P{ Xor ?a ?b } ==! ] ;


! NOTE: The third missing one is resolving a unit into a recursive call
! { 2 P{ ?TypeOf [ myloop ] ?tau1 } }
! { 3 P{ TypeOfWord myloop ?sig1 } }
! { 4 P{ ?TypeOf [ [ call ] keep swap [ myloop ] [ drop ] if ] ?sig1 } }
! { 95 P{ ?TypeOf [ [ myloop ] ] ?rho13 } }
! { 97 P{ Recursion myloop ?rho14 ?tau1 } }
! { 98 P{ MakeUnit ?rho14 ?sig18 } }
! { 99 P{ TypeOf [ [ myloop ] ] ?sig18 } }
! {
!     165
!     P{
!         ComposeType
!         ?rho13
!         P{
!             Xor
!             P{ Effect L{ ?p4 ?c4 . ?a34 } ?b11 { P{ CallEffect ?p4 ?a34 ?b11 } P{ Instance ?c4 not{ ~wrapper~ } } P{ Use ?c4 } } }
!             P{ Effect L{ ?p5 ?c5 ?x29 . ?b12 } ?b12 { P{ Instance ?c5 W{ f } } P{ Drop ?x29 } P{ Drop ?p5 } P{ Use ?c5 } } }
!         }
!         ?z15
!     }
! }
CHR: resolve-rec-make-unit-tail @ { MakeUnit ?rho ?sig } { TypeOf ?x ?sig } { Recursion ?l ?rho ?tau } //
{ ?TypeOf ?x ?c }
--
[ ?rho term-var? ]
[ ?tau term-var? ]
[ ?sig term-var? ] |
[ ?c
  P{ Effect ?a L{ ?q . ?a } {
         P{ Instance ?q P{ Effect ?i ?o { P{ CallRecursive ?l ?i ?o } } } }
         P{ Literal ?q }
     } }
  ==!
] ;


! Target of unit constructor is unknown in recursive partial type
! { 35 P{ TypeOf [ mylastcdr ] P{ Xor P{ Effect ?a3 ?a3 { P{ Declare L{ L{ } } ?a3 } } } ?rho4 } } }
! { 4 P{ TypeOfWord mylastcdr P{ Xor P{ Effect ?a3 ?a3 { P{ Declare L{ L{ } } ?a3 } } } ?rho4 } } }
! { 6 P{ TypeOfWord M\ L{ } mylastcdr P{ Effect ?a3 ?a3 { P{ Declare L{ L{ } } ?a3 } } } } }
! { 39 P{ MakeUnit ?rho4 ?sig9 } }
! {
!     25
!     P{
!         Recursion
!         [ [ mylastcdr ] ]
!         ?rho8
!         P{ Xor P{ Effect ?a8 L{ ?x1 . ?a8 } { P{ Instance ?x1 P{ Effect ?a3 ?a3 ~array~ } } P{ Literal ?x1 } } } ?sig9 }
!     }
! }
! { 27 P{ ComposeType ?rho8 P{ Effect L{ ?q1 . ?a7 } ?b1 { P{ CallEffect ?q1 ?a7 ?b1 } } } ?z2 } }
CHR: resolve-rec-make-unit @ { MakeUnit ?tau ?sig } // { Recursion ?l ?x ?e } --
[ ?tau term-var? ]
[ ?sig term-var? ]
[ ?sig ?e free-effect-vars in? ] |
[| | ?e { { ?sig ?rho } } lift :> rectype
 P{ Recursion ?l ?x rectype }
]
[ ?rho
  P{ Effect ?a L{ ?q . ?a } {
         P{ Instance ?q P{ Effect ?i ?o { P{ CallRecursive ?l ?i ?o } } } }
         P{ Literal ?q }
     } }
  ==!
] ;

;

: qt ( quot -- res )
    InferType boa 1array chr-comp swap [ run-chr-query store>> ] with-var-names ;
