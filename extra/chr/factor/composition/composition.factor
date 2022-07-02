USING: accessors arrays assocs chr chr.factor chr.parser chr.state classes
classes.algebra classes.tuple classes.tuple.private combinators
combinators.short-circuit effects generic generic.single kernel kernel.private
lists macros math math.parser quotations sequences sequences.private sets
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

TUPLE: Literal < chr-pred val ;
TUPLE: Slot < chr-pred obj n val ;
TUPLE: Element < chr-pred obj type ;
TUPLE: Length < chr-pred obj val ;
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
TUPLE: Continue < chr-pred tag ;
TUPLE: Recursion < chr-pred tag back-to from ;
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

! TUPLE: Use < chr-pred val ;
TUPLE: Let < chr-pred var val type ;

TUPLE: Invalid < chr-pred ;

! Arithmetic Reasoning
! FIXME: for some reason, this doesnt pick up correctly if it is a union def...
! UNION: expr-pred Abs Sum Eq Le Lt Ge Gt ;
TUPLE: expr-pred < chr-pred ;
TUPLE: Abs < expr-pred val var ;
TUPLE: Sum < expr-pred val summand1 summand2 ;
TUPLE: Eq < expr-pred val var ;
TUPLE: Neq < expr-pred val var ;
TUPLE: Le < expr-pred val var ;
TUPLE: Lt < expr-pred val var ;
! TUPLE: Ge < expr-pred val var ;
! TUPLE: Gt < expr-pred val var ;


: word-alias ( word -- def/f )
    H{
        { rot [ [ swap ] dip swap ] }
        { over [ swap dup [ swap ] dip ] }
        { call [ (call) ] }
        { nip [ [ drop ] dip ] }
        { 2drop [ drop drop ] }
        { 3drop [ drop drop drop ] }
        { 2dup [ over over ] }
        { 3dup [ pick pick pick ] }
        { 2dip [ swap [ dip ] dip ] }
        { 3dip [ swap [ 2dip ] dip ] }
        { -rot [ swap [ swap ] dip ] }
        { if [ ? call ] }
        { loop [ [ call ] keep swap [ loop ] [ drop ] if ] }
        { pick [ [ over ] dip swap ] }
        { > [ swap < ] }
        { <= [ 2dup < [ 2drop t ] [ = ] if ] }
        { >= [ swap <= ] }
    } at ;

CHRAT: chr-comp { TypeOf }


! Tag-level concrete type!
! ** Type Definitions
CHR: start-type-of @ // { InferType ?q } -- | { ?TypeOf ?q ?tau } ;

CHR: unique-type @ { TypeOf ?x ?tau } // { TypeOf ?x ?tau } -- | ;

GENERIC: free-effect-vars ( term -- term )
: full-type? ( type -- ? ) free-effect-vars empty? ;

CHR: conflicting-type @ { TypeOf ?x ?tau } // { TypeOf ?x ?sig } -- [ ?tau full-type? ] [ ?sig full-type? ] | [ "conflicting type-defs" throw f ] ;

CHR: have-recursive-type @ // { Recursion ?x __ ?sig } { TypeOf ?x ?rho } { ?TypeOf ?x ?sig } -- |
[ ?sig ?rho ==! ] ;

CHR: answer-type @ { TypeOf ?x ?tau } // { ?TypeOf ?x ?sig } -- [ ?tau full-type? ] | [ ?sig ?tau ==! ] ;

TUPLE: PushdownRec < chr-pred label val type ;


CHR: double-word-inference @ { ?TypeOf [ ?x ] ?tau } // { ?TypeOf [ ?x ] ?sig } -- [ ?tau term-var? ] [ ?sig term-var? ]
[ ?x callable-word? ] |
[ ?sig P{ Effect ?a ?b { { P{ CallRecursive ?x ?a ?b } } } } ==! ] ;

CHR: double-inference-queue @ { ?TypeOf ?x ?tau } { ?TypeOf ?x ?sig } // -- [ ?tau term-var? ] [ ?sig term-var? ] |
{ Recursion ?x ?tau ?sig } ;

CHR: alias-type-defined @ { TypeOfWord ?w ?tau } // -- [ ?w word-alias :>> ?q ] |
{ ?TypeOf ?q ?tau } ;

CHR: type-of-prim-call @ // { ?TypeOf [ (call) ] ?tau } -- |
[ ?tau P{ Effect L{ ?q . ?a } ?b {
              P{ Instance ?q callable }
              P{ CallEffect ?q ?a ?b } } } ==! ] ;

CHR: type-of-dip @ { TypeOfWord dip ?tau } // -- |
[ ?tau P{ Effect L{ ?q ?x . ?a } L{ ?x . ?b } { P{ CallEffect ?q ?a ?b } } } ==! ] ;

CHR: type-of-dup @ { TypeOfWord dup ?tau } // -- |
[ ?tau P{ Effect L{ ?x . ?rho } L{ ?x ?x . ?rho } f } ==! ] ;

CHR: type-of-drop @ // { ?TypeOf [ drop ] ?tau } -- |
[ ?tau P{ Effect L{ ?x . ?a } ?a f } ==! ] ;

CHR: type-of-swap @ // { ?TypeOf [ swap ] ?tau } -- |
[ ?tau P{ Effect L{ ?x ?y . ?a } L{ ?y ?x . ?a } f } ==! ] ;

CHR: type-of-mux @ // { ?TypeOf [ ? ] ?tau } -- |
[
    ?tau
    P{ Xor
       P{ Effect L{ ?q ?p ?c . ?a } L{ ?p . ?a } { P{ Instance ?c not{ W{ f } } } } }
       P{ Effect L{ ?q ?p ?c . ?a } L{ ?q . ?a } { P{ Instance ?c W{ f } } } }
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
        } }
     P{ Effect L{ ?x . ?a } L{ ?y . ?a } {
            P{ Instance ?x ?d }
            P{ Literal ?y }
            P{ Instance ?y W{ f } }
        } }
   }
  ==!
] ;

! : nth-unsafe ( n seq -- elt )
! NOTE: existentials
CHR: type-of-access @ { TypeOfWord array-nth ?tau } // -- |
[ ?tau
  P{ Effect L{ ?n ?l . ?a } L{ ?v . ?a } {
         P{ Instance ?n fixnum }
         P{ Instance ?l array }
         P{ Instance ?x array-capacity }
         P{ Length ?l ?x }
         ! P{ Gt ?x ?n }
         P{ Le ?n ?x }
         P{ Element ?l ?v }
     } }
  ==! ] ;

! : slot ( obj m -- value )
CHR: type-of-slot @ { TypeOfWord slot ?tau } // -- [ ?tau term-var? ] |
[ ?tau
  P{ Effect L{ ?m ?o . ?a } L{ ?v . ?a } {
         P{ Instance ?m fixnum }
         P{ Slot ?o ?m ?v }
     } }
  ==! ] ;

! : set-slot ( value obj n -- )
CHR: type-of-set-slot @ { TypeOfWord set-slot ?tau } // -- [ ?tau term-var? ] |
[ ?tau
  P{ Effect L{ ?v ?o ?n . ?a } ?a {
         P{ Instance ?n fixnum }
         P{ Slot ?o ?n ?v }
     } }
  ==!
] ;


CHR: type-of-throw @ // { ?TypeOf [ throw ] ?tau } -- |
! [ ?tau P{ Effect ?a +bottom+ f } ==! ] ;
! [ ?tau null ==! ] ;
[ ?tau P{ Effect L{ ?e . ?a } L{ ?e . ?a } {
              P{ Throws ?e }
              ! P{ Invalid }
          } }
  ==! ] ;

CHR: type-of-boa @ // { ?TypeOf [ boa ] ?tau } -- |
[ ?tau
  P{ Effect L{ ?c . ?a } L{ ?v . ?b } { P{ Instance ?c tuple-class } P{ Boa ?c ?a L{ ?v . ?b } }
                                        P{ Instance ?v tuple } } }
  ==!
] ;

CHR: type-of-tuple-boa @ // { ?TypeOf [ <tuple-boa> ] ?tau } -- |
[ ?tau
  P{ Effect L{ ?c . ?a } L{ ?v . ?b } { P{ Instance ?c array } P{ TupleBoa ?c ?a L{ ?v . ?b } }
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
{ TypeOf ?q ?sig } ;

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
     } }
  ==! ] ;

! CHR: type-of-fixnum+ @ { TypeOfWord fixnum+ ?tau } // -- |
! [ ?tau
!   P{ Effect L{ ?x ?y . ?a } L{ ?z . ?b } { P{ Instance ?x fixnum } P{ Instance ?y fixnum } P{ Use ?x } P{ Use ?y } P{ Instance ?z integer } } }
!   ==!
! ] ;

! *** Math
CHR: type-of-+ @ { TypeOfWord A{ + } ?tau } // -- |
[ ?sig
  P{ Effect L{ ?x ?y . ?a } L{ ?z . ?a } {
         P{ Instance ?z number }
         P{ Sum ?z ?x ?y }
     } }
  ==! ]
{ ComposeType P{ Effect ?a ?a { P{ Declare { number number } ?a } } } ?sig ?tau } ;

CHR: type-of-< @ { TypeOfWord A{ < } ?tau } // -- |
[
    ?sig
    P{ Xor
       P{ Effect L{ ?x ?y . ?a } L{ ?z . ?a } {
              P{ Literal ?z }
              P{ Instance ?z W{ t } }
              P{ Lt ?y ?x }
              ! P{ Neq ?y ?x }
          } }
        P{ Effect L{ ?x ?y . ?a } L{ ?z . ?a }  {
               P{ Literal ?z }
               P{ Instance ?z W{ f } }
               P{ Le ?x ?y }
           } }
     }
    ==!
]
{ ComposeType P{ Effect ?a ?a { P{ Declare { number number } ?a } } } ?sig ?tau } ;

CHR: type-of-= @ { TypeOfWord A{ = } ?tau } // -- |
[
    ?sig
    P{ Xor
       P{ Effect L{ ?x ?y . ?a } L{ ?z . ?a } {
              P{ Literal ?z }
              P{ Instance ?z W{ t } }
              P{ Eq ?x ?y }
          } }
       P{ Effect L{ ?x ?y . ?a } L{ ?z . ?a }  {
              P{ Literal ?z }
              P{ Instance ?z W{ f } }
              P{ Neq ?y ?x }
          } }
     }
    ==!
]
{ ComposeType P{ Effect ?a ?a { P{ Declare { number number } ?a } } } ?sig ?tau } ;

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
[ ?w def>> ?w 1quotation = not ]
[ ?w def>> :>> ?q ]
[ ?w "input-classes" word-prop >array :>> ?c ]
|
{ ?TypeOf ?q ?sig }
{ ComposeType P{ Effect ?a ?a { P{ Declare ?c ?a } } } ?sig ?tau } ;

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
{ MakeXor ?rho ?sig ?tau } ;


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
! ** Phi Reasoning

! Approach: A complete xor can be checked for whether parallel application
! results in disjoint types.  If so, it is indeed an XOR.  If not, generate a union
! type.  The reasoning is as follows: The XOR case is really only interesting
! for disjoint reasoning if we can be sure that applying one set of input/output
! types actually excludes the other alternative.  If we get overlapping types,
! then the intersection is not-empty, and the best we can do is reason with the convex cover.
! Note that this strategy here is eager, so it will be re-done for every layer of xor for now...

TUPLE: CheckXor < chr-pred then else target ;
TUPLE: PhiSchedule < chr-pred list target ;
TUPLE: DisjointRoot < chr-pred effect ;
TUPLE: DestrucXor < chr-pred branch ;
TUPLE: RebuildXor < chr-pred effect target ;
TUPLE: CurrentPhi < chr-pred effect ;
TUPLE: MakeUnion < chr-pred effect1 effect2 target ;
TUPLE: IsUnion < chr-pred pred ;
TUPLE: PhiMode < chr-pred ;
TUPLE: PhiDone < chr-pred ;

! Catch
CHR: maybe-make-trivial-xor @ // { MakeXor ?rho ?sig ?tau } -- [ ?rho full-type? ] [ ?sig full-type? ] |
[ ?rho ?sig isomorphic?
  [ ?tau ?rho ==! ]
  ! [ ?tau P{ Xor ?rho ?sig } ==! ]
  { CheckXor ?rho ?sig ?tau } ?
] ;

! Some sanity checks
CHR: xor-error @ <={ CheckXor } <={ CheckXor } // -- | [ "xor sequencing error" throw ] ;
CHR: phi-error @ <={ PhiSchedule } <={ PhiSchedule } // -- | [ "phi sequencing error" throw ] ;
CHR: current-phi-error @ { CurrentPhi __ } { CurrentPhi __ } // -- | [ "current phi sequencing error" throw ] ;
CHR: make-union-error @ <={ MakeUnion } <={ MakeUnion } // -- | [ "double make-union" throw ] ;

! Start Destructuring, trigger schedule
CHR: check-xor @ // { CheckXor ?rho ?sig ?tau } -- [ ?rho full-type? ] [ ?sig full-type? ] |
{ DestrucXor ?rho }
{ DestrucXor ?sig }
{ PhiSchedule +nil+ ?tau } ;

CHR: destruc-rebuild-xor @ // { DestrucXor P{ Xor ?a ?b } } -- |
{ DestrucXor ?a } { DestrucXor ?b } ;
CHR: destruc-rebuild-effect @ // { PhiSchedule ?r ?tau } { DestrucXor ?e } -- [ ?e Effect? ] |
{ PhiSchedule L{ ?e . ?r } ?tau } ;

! Triggers actual phi-reasoning
CHR: try-next-phi @ { CurrentPhi ?a } P{ PhiSchedule L{ ?b . ?r } __ } // -- |
[| |
 ?a fresh-effect :> e1
 ?b fresh-effect :> e2
 { MakeUnion e1 e2 ?tau } ] ;

! Finished Schedules
CHR: all-phis-done @ { PhiSchedule +nil+ ?tau } // { DisjointRoot ?a } -- |
{ RebuildXor ?a ?tau } ;

CHR: try-union-effect @ { MakeUnion ?a ?b ?tau } // -- [ ?tau term-var? ] |
{ PhiMode }
{ ComposeEffect ?a ?b ?tau } ;

! After MakeEffect has finished
CHR: have-union-effect @ // { DisjointRoot ?e } { CurrentPhi ?e } { MakeUnion __ __ ?a } { PhiDone } { PhiSchedule L{ ?b . ?r } ?tau } --
[ ?a Effect? ] | { DisjointRoot ?a } { PhiSchedule ?r ?tau } ;

CHR: have-disjoint-effect @ // { CurrentPhi ?e } { MakeUnion __ __ null } { PhiDone } -- | ;

CHR: try-next-phi-merge @ { DisjointRoot ?e } { PhiSchedule L{ ?b . ?r } __ } // -- | { CurrentPhi ?e } ;

CHR: no-next-phi-merge @ // { PhiSchedule L{ ?b . ?r } ?tau } -- |
{ DisjointRoot ?b } { PhiSchedule ?r ?tau } ;

! *** Rebuild after intersection checking
CHR: rebuild-phi-collect-branch @ { PhiSchedule +nil+ ?tau } // { RebuildXor ?a ?tau } { DisjointRoot ?b } -- |
{ RebuildXor P{ Xor ?a ?b } ?tau } ;

CHR: rebuild-phi-finished @ // { PhiSchedule +nil+ ?tau } { RebuildXor ?a ?tau } -- |
[ ?tau ?a ==! ] ;

! ! *** Start intersection checking
! CHR: try-phi-schedule @ // { CheckXor __ __ ?tau } { PhiSchedule L{ ?e . ?r } ?tau } -- |
! { DisjointRoot ?e } { PhiSchedule ?r ?tau } ;


! CHR: make-xor @ // { MakeXor ?rho ?sig ?tau } --
! ! [ ?rho term-var? not ?sig term-var? not or ]
! [ ?rho term-var? not ] [ ?sig term-var? not ]
! | [ ?tau P{ Xor ?rho ?sig } ==! ] ;


! ** Simplification/Intra-Effect reasoning

UNION: val-pred Instance Literal Slot CallEffect ;
UNION: body-pred Instance CallEffect Literal Declare Slot CallRecursive Throws expr-pred ;

! *** Start unification reasoning
! NOTE: assumed renaming here already
CHR: rebuild-phi-effect @ { PhiMode } // { ComposeEffect P{ Effect ?a ?b ?k } P{ Effect ?c ?d ?l } ?tau } -- |
[ { ?a ?b } { ?c ?d } ==! ]
! NOTE: This happens if we have pre-defined effects but no known body yet (e.g. recursive calls)
! [ ?k dup term-var? [ drop f ] when ]
! [ ?l dup term-var? [ drop f ] when ]
[ ?k ]
[ ?l ]
{ MakeEffect ?a ?d f f ?tau } ;

CHR: rebuild-compose-effect @ // { ComposeEffect P{ Effect ?a ?b ?k } P{ Effect ?c ?d ?l } ?tau } -- |
[ ?b ?c ==! ]
! NOTE: This happens if we have pre-defined effects but no known body yet (e.g. recursive calls)
! [ ?k dup term-var? [ drop f ] when ]
! [ ?l dup term-var? [ drop f ] when ]
[ ?k ]
[ ?l ]
{ MakeEffect ?a ?d f f ?tau } ;


CHR: early-exit @ { Invalid } // <={ body-pred } -- | ;

! *** <Phi
CHR: same-stays-valid @ { PhiMode } // AS: ?p <={ body-pred } AS: ?q <={ body-pred } -- [ ?p ?q == ] |
{ IsUnion ?p } ;

! NOTE: this is pretty tricky with regards to what constitutes valid criteria for /not/
! merging types during phi reasoning.  Couple of approaches:
! 1. Any joined type, be it input, internal, or output is considered to be in covariant position
! 2. Only output types are considered to be in covariant position
! 3. Some explicit dependency type magic determines under what conditions we want to be distinct...
CHR: phi-disjoint-instance @ { PhiMode } { MakeEffect ?a ?b __ __ __ } // { Instance ?x A{ ?rho } } { Instance ?x A{ ?tau } } --
[ ?x ?b vars in? ] [ { ?rho ?tau } first2 classes-intersect? not ] | { Invalid } ;

! ( x <= 5 ) ( 5 <= x ) -> union
! ( x <= 4 ) ( 5 <= x ) -> disjoint
! ( x <= 5 ) ( 4 <= x ) -> union
CHR: phi-disjoint-output-range-le-le @ { PhiMode } // { Le ?x A{ ?m } } { Le A{ ?n } ?x } --
[ ?m ?n < ] | { Invalid } ;
! ( x < 5 ) ( 5 <= x ) -> disjoint
! ( x < 4 ) ( 5 <= x ) -> disjoint
! ( x < 5 ) ( 4 <= x ) -> union
CHR: phi-disjoint-output-range-lt-le @ { PhiMode } // { Lt ?x A{ ?m } } { Le A{ ?n } ?x } --
[ ?m ?n <= ] | { Invalid } ;
CHR: phi-disjoint-output-range-le-lt @ { PhiMode } // { Le ?x A{ ?m } } { Lt A{ ?n } ?x } --
[ ?m ?n <= ] | { Invalid } ;
! ( x < 5 ) ( 5 < x ) -> disjoint
! ( x < 4 ) ( 5 < x ) -> disjoint
! ( x < 5 ) ( 4 < x ) -> union
CHR: phi-disjoint-output-range-lt-lt @ { PhiMode } // { Le ?x A{ ?m } } { Lt A{ ?n } ?x } --
[ ?m ?n <= ] | { Invalid } ;
CHR: phi-disjoint-output-range-lt-eq @ { PhiMode } // { Eq ?x A{ ?n } } { Lt ?x A{ ?n } } -- | { Invalid } ;

CHR: phi-effect-instance @ { PhiMode } // { Instance ?x P{ Effect __ __ __ } } -- | { Invalid } ;

CHR: phi-instance @ { PhiMode } // { Instance ?x A{ ?rho } } { Instance ?x A{ ?sig } } --
[ { ?rho ?sig } first2 class-or :>> ?tau ] |
{ IsUnion P{ Instance ?x ?tau } } ;

CHR: phi-call-effect @ { PhiMode } // AS: ?p P{ CallEffect ?q ?a ?b } { CallEffect ?q ?x ?y } -- [ { ?a ?b } { ?x ?y } unify ] |
[ { ?a ?b } { ?x ?y } ==! ]
{ IsUnion ?p } ;
CHR: is-inline-effect @ { PhiMode } // <={ CallEffect } -- | { Invalid } ;

! *** Phi>

! TODO: extend to other body preds
CHR: unique-instance @ { Instance ?x ?tau } // { Instance ?x ?tau } -- | ;

CHR: uniqe-slot @ { Slot ?o ?n ?v } // { Slot ?o ?n ?v } -- | ;

! NOTE: the reasoning is that this can inductively only happen during composition of two straight-line
! effects. So the instance in the first one is a "provide", and the instance in the second one is an "expect".
! Since the intersection type operation is commutative, we don't care which came from which.
CHR: same-slot-must-be-same-var @ { Slot ?o ?n ?v } // { Slot ?o ?n ?w } -- | [ ?v ?w ==! ] ;

CHR: useless-instance @ // { Instance __ object } -- | ;

CHR: null-instance-is-invalid @ { Instance __ null } // -- | { Invalid } ;

CHR: instance-intersection @ // { Instance ?x A{ ?tau } } { Instance ?x A{ ?sig } } -- [ { ?tau ?sig } first2 class-and :>> ?c ] |
{ Instance ?x ?c } ;

CHR: instance-intersect-effect @ { Instance ?x ?e  } { Literal ?x } // { Instance ?x A{ ?tau } } --
[ ?e valid-effect-type? ] |
[ ?tau callable eq? ?tau quotation eq? or
 f { Invalid } ? ] ;


CHR: invalid-stays-invalid @ { Invalid } // { Invalid } -- | ;

CHR: call-null-instance-is-invalid @ { CallEffect ?x __ __ } { Instance ?x null } // -- | { Invalid } ;

! *** Arithmetics
CHR: normlize-eq @ // { Eq A{ ?v } ?x } -- [ ?x term-var? ] | { Eq ?x ?v } ;
CHR: check-le @ // { Le A{ ?x } A{ ?y } } -- [ ?x ?y <= not ] | { Invalid } ;
CHR: check-lt @ // { Lt A{ ?x } A{ ?y } } -- [ ?x ?y < not ] | { Invalid } ;
CHR: le-defines-eq @ // { Le ?x ?y } { Le ?y ?x } -- | { Eq ?x ?y } ;
CHR: lt-defines-neq @ // { Lt ?x ?y } { Lt ?y ?x } -- | { Neq ?x ?y } ;
CHR: check-lt @ // { Lt ?x ?y } { Lt ?y ?x } -- | { Invalid } ;
CHR: check-lt-eq-1 @ // { Lt ?x ?y } { Eq ?x ?y } -- | { Invalid } ;
CHR: check-lt-eq-2 @ // { Lt ?x ?y } { Eq ?y ?x } -- | { Invalid } ;
CHR: check-eq-1 @ // { Eq ?x ?y } { Neq ?x ?y } -- | { Invalid } ;
CHR: check-eq-2 @ // { Eq ?x ?y } { Neq ?y ?x } -- | { Invalid } ;
CHR: check-neq @ // { Neq A{ ?x } A{ ?y } } -- [ ?x ?y == ] | { Invalid } ;

CHR: check-sum @ // { Sum A{ ?z } A{ ?x } A{ ?y } } -- [ ?x ?y + ?z = not ] | P{ Invalid } ;

CHR: define-sum @ // { Sum ?z A{ ?x } A{ ?y } } --
[ ?x ?y + <wrapper> :>> ?v ] |
P{ Instance ?z ?v } ;

! *** Call Effect matching
! NOTE: These only meet in renamed form?
! NOTE: not sure this has to be restricted to literals, actually, but it feels like we would
! violate the unknown-call safety net...
CHR: call-applies-effect @ { Literal ?q } { Instance ?q P{ Effect ?c ?d ?l } } { CallEffect ?q ?a ?b } // -- |
[ { ?a ?b } { ?c ?d } ==! ] [ ?l ] ;

CHR: call-destructs-curry @ { Instance ?q curried } { Slot ?q "quot" ?p } { Slot ?q "obj" ?x } // { CallEffect ?q ?a ?b } -- |
{ CallEffect ?p L{ ?x . ?a } ?b } ;

CHR: call-destructs-composed @ { Instance ?p composed } { Slot ?p "first" ?q } { Slot ?p "second" ?r } // { CallEffect ?p ?a ?b } -- |
{ CallEffect ?q ?a ?rho } { CallEffect ?r ?rho ?b } ;

! *** Declarations

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

! NOTE: this is still a bit tedious...Maybe we can have nice things? (Directly substitute literals...)
! CHR: known-expr-val @ { Literal ?n } { Instance ?n A{ ?v } } // AS: ?p <={ expr-pred } -- [ ?n ?p vars in? ]
CHR: known-expr-val @ { Instance ?n ?v } // AS: ?p <={ expr-pred } -- [ ?n ?p vars in? ]
[ { ?v } first wrapper? ]
[ { ?v } first wrapped>> :>> ?w ]
|
[ ?p { { ?n ?w } } lift* ] ;

! *** Slot conversion
CHR: known-named-slot @ { Instance ?o A{ ?tau } } // { Slot ?o A{ ?n } ?v } -- [ ?tau tuple-class? ]
[ ?tau all-slots [ offset>> ?n = ] find nip :>> ?s ] [ ?s name>> :>> ?m ]
[ ?s class>> :>> ?rho ]
|
{ Slot ?o ?m ?v }
{ Instance ?v ?rho } ;

CHR: known-boa-spec @ { Instance ?c A{ ?v } } { Literal ?c } // AS: ?p <={ Boa ?c ?i ?o } -- |
[ ?p ?v >>spec ] ;

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

! ** Post-Reasoning
! All of these must be live to take collecting the pred into account
GENERIC: live-vars ( pred -- vars )
GENERIC: defines-vars ( pred -- vars )
M: chr-pred live-vars vars ;
M: object defines-vars drop f ;
M: CallEffect live-vars thing>> 1array ;
M: CallEffect defines-vars [ in>> vars ] [ out>> vars ] bi union ;
M: Slot live-vars obj>> 1array ;
M: Slot defines-vars [ n>> ] [ val>> ] bi 2array ;
M: Instance live-vars id>> 1array ;
M: Instance defines-vars type>> defines-vars ;

! *** Phi Mode
CHR: discard-non-union-pred @ { PhiMode } <={ MakeEffect } // <={ body-pred } -- | ;

CHR: collect-union-preds @ { PhiMode } // { MakeEffect ?a ?b f ?l ?tau } { IsUnion ?p } --
[ ?l ?p suffix :>> ?k ] |
{ MakeEffect ?a ?b f ?k ?tau } ;

! *** Composition Mode
! These are live after the pred has been taken into account
! *** Dead-value cleanup
! Used for values with folding semantics
TUPLE: Dead < chr-pred val ;
! CHR: unref @ <={ MakeEffect } // { Use ?x } { Literal ?x } -- | { Dead ?x } ;


: effect-vars ( make-effect -- set )
    [ in>> vars ] [ out>> vars union ] [ locals>> vars union ] tri ;

! existentials
! CHR: collect-type-ofs @ // AS: ?e P{ MakeEffect ?a ?b ?x ?l ?tau } { TypeOf ?v ?rho } --
! [ ?v ?e effect-vars in? ]
! [ ?l P{ TypeOf ?v ?rho } suffix :>> ?k ] |
! { MakeEffect ?a ?b ?x ?k ?tau } ;

! CHR: collect-nested-call-effect @ // AS: ?e P{ MakeEffect ?a ?b ?x ?l ?tau } AS: ?p P{ CallEffect ?q ?rho ?sig } --
! [ ?q ?e effect-vars in? ]
! [ ?x ?rho vars ?sig vars union union :>> ?y ]
! [ ?l ?p suffix :>> ?k ]
! | { MakeEffect ?a ?b ?y ?k ?tau } ;

! CHR: collect-call-recursive-input @ // AS: ?e P{ MakeEffect ?a ?b ?x ?l ?tau } AS: ?p P{ CallRecursive ?m ?rho ?sig } --
! [ ?rho vars ?e effect-vars subset? ]
! [ ?x ?sig vars union :>> ?y ]
! [ ?l ?p suffix :>> ?k ]
! | { MakeEffect ?a ?b ?y ?k ?tau } ;

! NOTE: The only time for now where this was needed instead of the one above was for [ t ] loop...
CHR: collect-call-recursive @ // AS: ?e P{ MakeEffect ?a ?b ?x ?l ?tau } AS: ?p P{ CallRecursive ?m ?rho ?sig } --
[ ?rho vars ?sig vars union ?e effect-vars intersects? ]
[ ?x ?rho vars union ?sig vars union :>> ?y ]
[ ?l ?p suffix :>> ?k ]
| { MakeEffect ?a ?b ?y ?k ?tau } ;

! CHR: collect-instance @ // AS: ?e P{ MakeEffect ?a ?b ?x ?l ?tau } P{ Instance ?v ?rho } --
! [ ?v ?e effect-vars in? ]
! [ ?l P{ Instance ?v ?rho } suffix :>> ?k ]
! | { MakeEffect ?a ?b ?x ?k ?tau } ;

! CHR: collect-call-recursive @ // AS: ?e P{ MakeEffect ?a ?b ?x ?l ?tau } AS: ?p P{ CallRecursive __ __ __ } --
! [ ?l ?p suffix :>> ?k ]
! | { MakeEffect ?a ?b ?x ?k ?tau } ;

! *** All other preds
! CHR: collect-body-pred @ // AS: ?e P{ MakeEffect ?a ?b ?x ?l ?tau } AS: ?p <={ body-pred } -- [ ?p vars ?e effect-vars intersects? ]
CHR: collect-body-pred @ // AS: ?e P{ MakeEffect ?a ?b ?x ?l ?tau } AS: ?p <={ body-pred } -- [ ?p live-vars ?e effect-vars subset? ]
[ ?l ?p suffix :>> ?k ]
|
[| | ?p defines-vars ?x union :> y
 { MakeEffect ?a ?b y ?k ?tau } ] ;

! CHR: collect-slot-defs @ // AS: ?e P{ MakeEffect ?a ?b ?x ?l ?tau } AS: ?p P{ Slot ?o ?n ?v } --
! [ ?o ?e effect-vars in? ]
! [ ?l ?p suffix :>> ?k ]
! [ ?x ?n vars union ?v vars union :>> ?y ] |
! { MakeEffect ?a ?b ?y ?k ?tau } ;

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

! TODO: check whether this is even applicable...
CHR: catch-unit-effect-call @ // { MakeEffect ?a ?b f f ?tau } { Literal ?q } { Instance ?q ?rho } { CallEffect ?q ?a ?b } --
[ ?rho term-var? not ]
[ ?a term-var? ] [ ?b term-var? ] |
[ ?tau ?rho ==! ] ;

CHR: conflicting-makes @ { MakeEffect __ __ __ __ __ } { MakeEffect __ __ __ __ __ } // -- | [ "recursive-make" throw f ] ;

! CHR: dead-val-pred @ <={ MakeEffect } { Dead ?v } // <={ val-pred ?v . __ } -- | ;
! CHR: cleanup-dead @ { MakeEffect __ __ __ __ __ } // { Dead __ } -- | ;

! *** Sanity check
! CHR: must-cleanup @ { MakeEffect __ __ __ __ __ } AS: ?p <={ body-pred } // -- | [ ?p "leftovers" 2array throw f ] ;
CHR: cleanup-incomplete @ { MakeEffect __ __ __ __ __ } // <={ body-pred } -- | ;

CHR: finish-invalid-effect @ { MakeEffect __ __ __ __ ?tau } // { Invalid } -- |
[ ?tau null ==! ] ;

CHR: finish-valid-effect @ { MakeEffect ?a ?b __ ?l ?tau } // -- [ ?tau term-var? ] |
[ ?tau P{ Effect ?a ?b ?l } ==! ] ;

CHR: finish-phi-reasoning @ // { MakeEffect __ __ __ __ ?tau } { PhiMode } -- [ ?tau term-var? not ] | { PhiDone } ;
CHR: finish-compositional-reasoning @ // { MakeEffect __ __ __ __ ?tau } -- [ ?tau term-var? not ] | ;

;

: qt ( quot -- res )
    InferType boa 1array chr-comp swap [ run-chr-query store>> ] with-var-names ;
