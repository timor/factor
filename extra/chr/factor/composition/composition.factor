USING: accessors arrays assocs chr chr.factor chr.modular chr.parser chr.state
classes classes.algebra classes.builtin classes.predicate classes.singleton
classes.tuple classes.tuple.private classes.union combinators
combinators.short-circuit effects generic generic.single kernel kernel.private
lists math math.parser math.private namespaces quotations sequences
sequences.private sets slots.private sorting strings terms types.util vectors
words words.symbol ;

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

! ** Effect Type
! An effect type would represent a typed Factor Effect
! ~( ..a x: integer y: number -- y x ..a )~  as
! #+begin_example factor
! P{ Effect L{ ?y ?x . ?a } L{ ?x ?y ?z . ?a } {
!   P{ Instance ?x integer }
!   P{ Instance ?y number }
!   }
! }
! #+end_example
! This is equivalent with the following logical expression:
! For all x, y, a, b: If the input matches the given form:
! - The output matches the given form
! - The value x is an instance of integer
! - The value y is an instance of number
! - We know nothing about the value ?z

! Problem: ~z~ could be interpreted as an existential variable, but also as a universally
! quantified one.  This is most interesting for union types, e.g. for the
! ~[ swap ] when~ example, where the union type of ~( x y -- y x )~ and
! ~( ..b -- ..b )~ has to be calculated.

! Now this is a bit problematic, concerning the semantics.
! The intersection check can be performed if we assume the same inputs, so firs we
! unify ~L{ ?y ?x . ?a } ==! ?b~.  This creates the following Effect Types:
! #+begin_example factor
! P{ Effect L{ ?y ?x . ?a } L{ ?x ?y . ?a } }
! P{ Effect L{ ?y ?x . ?a } L{ ?y ?x . ?a } }
! #+end_example

! Note that for making an intersection type, unification of this would actually be
! possible, and return the side condition that ~?x = ?y~.  However, the output
! stack itself can actually be considered a dependent type of the input stack.  In
! order for these to have the chance to intersect, they must be α-equivalent under
! the input stack bindings. (There can be existentials in the outputs)

TUPLE: Effect < chr-pred in out parms preds ;
! Placeholder-effect?
TUPLE: RecursiveEffect < chr-pred tag effect ;
TUPLE: TypeOf < chr-pred thing type ;
TUPLE: ?TypeOf < chr-pred thing type ;
TUPLE: FixpointTypeOf < chr-pred thing type ;
TUPLE: RecursionTypeOf < chr-pred thing type ;
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

TUPLE: Iterated < chr-pred init next end ;
! TUPLE: Iterated < chr-pred val end ;

! Value-restricting preds
TUPLE: val-pred < chr-pred val ;

TUPLE: Instance < val-pred type ;
TUPLE: NotInstance < Instance ;

TUPLE: Slot < val-pred n slot-val ;
TUPLE: Element < val-pred type ;
TUPLE: Length < val-pred length-val ;
! A declaration, has parameterizing character
TUPLE: Declare < chr-pred classes stack ;

! A declaration, has no parameterizing character, just shortcut for Instance
! constraints, used to ensure stack depths and instance decls
TUPLE: Ensure < chr-pred classes stack ;

TUPLE: CallEffect < chr-pred thing in out ;
TUPLE: MacroCallEffect < chr-pred word in out ;
TUPLE: CallRecursive < chr-pred tag in out ;
TUPLE: NullStack < chr-pred stack ;
TUPLE: RecursivePhi < chr-pred initial stepped end ;

TUPLE: Boa < chr-pred spec in id ;
TUPLE: TupleBoa < Boa ;
TUPLE: MacroArgs < chr-pred word in out ;
TUPLE: MacroCall < chr-pred quot args in out ;

! Macro expansion, folding
TUPLE: FoldStack < chr-pred stack n ;
TUPLE: FoldCall < chr-pred stack n quot target ;

! TUPLE: Recursive < chr-pred tag effect ;
TUPLE: Recursive < chr-pred tag ;
TUPLE: Continue < chr-pred tag ;
TUPLE: Recursion < chr-pred tag back-to from ;
TUPLE: MakeXor < chr-pred type1 type2 target ;

TUPLE: CheckXor < chr-pred quot branch target ;
TUPLE: MakeRecursion < chr-pred type target ;
TUPLE: MakeFoldable < chr-pred type target ;
TUPLE: Copy < chr-pred type target ;
TUPLE: CheckFixpoint < chr-pred quot type ;

TUPLE: Xor < chr-pred type1 type2 ;
TUPLE: And < chr-pred types ;
! TUPLE: Intersection < chr-pred type types ;
TUPLE: Intersection < chr-pred type types ;
TUPLE: Union < chr-pred type types ;
TUPLE: SubType < chr-pred sub super ;

! TUPLE: Use < chr-pred val ;
TUPLE: Let < chr-pred var val type ;

TUPLE: Invalid < chr-pred ;

TUPLE: Tag < val-pred tag-var ;

! Binding for explicit referencing
TUPLE: Bind < chr-pred var src ;

! Arithmetic Reasoning
! FIXME: for some reason, this doesnt pick up correctly if it is a union def...
! UNION: expr-pred Abs Sum Eq Le Lt Ge Gt ;
TUPLE: expr-pred < val-pred ;
TUPLE: Abs < expr-pred var ;
TUPLE: Sum < expr-pred summand1 summand2 ;
TUPLE: Prod < expr-pred factor1 factor2 ;
TUPLE: Shift < expr-pred in by ;
TUPLE: BitAnd < expr-pred in mask ;
TUPLE: Eq < expr-pred var ;
TUPLE: Neq < expr-pred var ;
TUPLE: Le < expr-pred var ;
TUPLE: Lt < expr-pred var ;
! TUPLE: Ge < expr-pred val var ;
! TUPLE: Gt < expr-pred val var ;
! Not math, but needed for types

: word-alias ( word -- def/f )
    H{
        { rot [ [ swap ] dip swap ] }
        { over [ swap dup [ swap ] dip ] }
        { call [ (call) ] }
        { nip [ [ drop ] dip ] }
        { 2nip [ nip nip ] }
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
        { - [ -1 * + ] }
    } at ;

! These are used as fallbacks for recursive calls to certain words
: rec-defaults ( word -- def/f )
    H{
        { length P{ Effect L{ ?a . ?r } L{ ?n . ?r } f {
                        P{ Instance ?a sequence }
                        P{ Length ?a ?n }
                    } } }
        { nth P{ Effect L{ ?n ?s . ?a } L{ ?v . ?a } f {
                     P{ Instance ?n integer }
                     P{ Lt 0 ?n }
                     P{ Instance ?s sequence }
                     P{ Element ?s ?v }
                 } } }
        { nth-unsafe P{ Effect L{ ?n ?s . ?a } L{ ?v . ?a } f {
                            P{ Instance ?n integer }
                            P{ Lt 0 ?n }
                            P{ Instance ?s sequence }
                            P{ Element ?s ?v }
                        } } }
    } at ;

! * CHR Program for Phi handling
TUPLE: PhiStack < chr-pred out part ;
TUPLE: Phi < chr-pred out part ;
TUPLE: ?Phi < chr-pred out then else phi-p ;
SINGLETONS: Yes No ;

CHRAT: chr-phi { ?Phi }
! ** Answer Phi Stack Queries
CHR: answer-have-phi @ { Phi ?z ?x } { Phi ?z ?y } // { ask { ?Phi ?v ?x ?y ?k } } -- |
[ ?v ?z ==! ] [ ?k Yes ==! ] { entailed { ?Phi ?v ?x ?y ?k } } ;
! NOTE: destructive
CHR: ask-phi-destruc-stack @ { Phi ?z ?x } { Phi ?z ?y } { ask { ?Phi ?v L{ ?x . ?xs } L{ ?y . ?ys } ?k } } // --
| [ ?v L{ ?z . ?zs } ==! ] ;
CHR: ask-phi-test-stack @ { Phi ?z ?x } { Phi ?z ?y } // { ask { ?Phi L{ ?z . ?zs } L{ ?x . ?xs } L{ ?y . ?ys } ?k } } --
{ ?Phi ?zs ?xs ?ys ?k } | { entailed { ?Phi L{ ?z . ?zs } L{ ?x . ?xs } L{ ?y . ?ys } ?k } } ;
CHR: ask-phi-is-no-phi @ // { ask { ?Phi ?z ?x ?y ?k } } -- | [ ?k No ==! ] { entailed { ?Phi ?z ?k ?y ?k } } ;


! ** Destructure Phi Specs
CHR: must-be-same-phi @ { Phi ?z ?x } { Phi ?z ?y } // { Phi ?v ?x } { Phi ?v ?y } -- | [ ?v ?z ==! ] ;

! CHR: phi-stack-done @ // { PhiStack ?z ?x } { PhiStack ?z ?y } -- [ ?x term-var? ] [ ?y term-var? ] [ ?z term-var? ] |
! [ ?x ?y ==! ] ;
! CHR: phi-stack-done @ // { PhiStack ?z ?x } { PhiStack ?z ?y } -- [ ?x term-var? ] [ ?y term-var? ] [ ?z term-var? ] | ;
CHR: phi-stack-done @ // { PhiStack ?z ?x } { PhiStack ?z ?y } -- [ ?x term-var? ] [ ?y term-var? ] [ ?z term-var? ] |
[ ?x ?y ==! ] [ ?z ?x ==! ] ;

CHR: phi-val @ // { PhiStack L{ ?z . ?zs } L{ ?x . ?xs } } { PhiStack L{ ?z . ?zs } L{ ?y . ?ys } } -- |
{ PhiStack ?zs ?xs } { PhiStack ?zs ?ys }
{ Phi ?z ?x } { Phi ?z ?y }
{ Instance ?z object } ;
! NOTE: destructive
CHR: phi-stack-expand @ { PhiStack ?a L{ ?x . ?xs } } { PhiStack ?a L{ ?y . ?ys } } // -- | [ ?a L{ ?z . ?zs } ==! ] ;
! NOTE: destructive
CHR: phi-balance @ { PhiStack ?z L{ ?x . ?xs } } { PhiStack ?z ?c } // -- | [ ?c L{ ?y . ?ys } ==! ] ;


;

! * CHR Program for Composition solving
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

CHR: double-word-inference-special @ { ?TypeOf [ ?x ] ?tau } // { ?TypeOf [ ?x ] ?sig } -- [ ?tau term-var? ] [ ?sig term-var? ]
[ ?x callable-word? ] [ ?x rec-defaults :>> ?e ] |
[ ?sig ?e ==! ] ;

CHR: double-word-inference @ { ?TypeOf [ ?x ] ?tau } // { ?TypeOf [ ?x ] ?sig } -- [ ?tau term-var? ] [ ?sig term-var? ]
[ ?x callable-word? ] |
[ ?sig P{ Effect ?a ?b f { { P{ CallRecursive ?x ?a ?b } } } } ==! ] ;
! [ ?sig P{ Effect ?a ?b f { P{ NullStack ?b } } } ==! ] ;

CHR: double-inference-queue @ { ?TypeOf ?x ?tau } { ?TypeOf ?x ?sig } // -- [ ?tau term-var? ] [ ?sig term-var? ] |
{ Recursion ?x ?tau ?sig } ;

CHR: alias-type-defined @ { TypeOfWord ?w ?tau } // -- [ ?w word-alias :>> ?q ] |
{ ?TypeOf ?q ?tau } ;

CHR: type-of-prim-call @ // { ?TypeOf [ (call) ] ?tau } -- |
[ ?tau P{ Effect L{ ?q . ?a } ?b f {
              P{ Instance ?q callable }
              P{ CallEffect ?q ?a ?b } } } ==! ] ;

CHR: type-of-dip @ { TypeOfWord dip ?tau } // -- |
[ ?tau P{ Effect L{ ?q ?x . ?a } L{ ?x . ?b } f { P{ CallEffect ?q ?a ?b } } } ==! ] ;

CHR: type-of-dup @ { TypeOfWord dup ?tau } // -- |
[ ?tau P{ Effect L{ ?x . ?rho } L{ ?x ?x . ?rho } f f } ==! ] ;

CHR: type-of-drop @ // { ?TypeOf [ drop ] ?tau } -- |
[ ?tau P{ Effect L{ ?x . ?a } ?a f f } ==! ] ;

CHR: type-of-swap @ // { ?TypeOf [ swap ] ?tau } -- |
[ ?tau P{ Effect L{ ?x ?y . ?a } L{ ?y ?x . ?a } f f } ==! ] ;

CHR: type-of-mux @ // { ?TypeOf [ ? ] ?tau } -- |
[
    ?tau
    P{ Xor
       P{ Effect L{ ?q ?p ?c . ?a } L{ ?p . ?a } { ?c } { P{ Instance ?c not{ W{ f } } } } }
       P{ Effect L{ ?q ?p ?c . ?a } L{ ?q . ?a } { ?c } { P{ Instance ?c W{ f } } } }
     }
    ==!
] ;

! CHR: type-of-builtin-predicate @ { TypeOfWord ?w ?tau } // -- [ ?w "predicating" word-prop :>> ?c ] [ ?c tuple-class? ?c builtin-class? or ] [ ?tau term-var? ] |
CHR: type-of-builtin-predicate @ // { ?TypeOf [ ?w ] ?tau } --
[ ?w word? ] [ ?w "predicating" word-prop :>> ?c ] [ ?c tuple-class? ?c builtin-class? or ] [ ?tau term-var? ]
[ ?c class-not :>> ?d ]
|
[| |
 ?tau
  P{ Xor
     ! P{ Effect L{ ?x . ?a } L{ ?y . ?a } { ?x ?y } {
     P{ Effect L{ ?x . ?a } L{ ?y . ?a } { ?y } {
            P{ Instance ?x ?c }
            P{ Instance ?y W{ t } }
        } }
     ! P{ Effect L{ ?x . ?a } L{ ?y . ?a } { ?x ?y } {
     P{ Effect L{ ?x . ?a } L{ ?y . ?a } { ?y } {
            P{ Instance ?x ?d }
            P{ Instance ?y W{ f } }
        } }
   }
  ==!
] ;

! NOTE: this is kind of a chicken-and-egg situation with instance checks.  There seems to
! be some kind of mutually recursive dependency between normative declaration and predicate
! checking.
CHR: type-of-instance? @ // { TypeOfWord instance? ?tau } -- |
[ ?tau P{ Xor
          ! P{ Effect L{ ?o ?sig . ?a } L{ ?c . ?a } { ?o ?c } {
          P{ Effect L{ ?o ?sig . ?a } L{ ?c . ?a } { ?c } {
                 P{ Instance ?o ?sig }
                 P{ Instance ?c W{ t } }
             } }
          ! P{ Effect L{ ?o ?sig . ?a } L{ ?c . ?a } { ?o ?c } {
          P{ Effect L{ ?o ?sig . ?a } L{ ?c . ?a } { ?c } {
                 P{ NotInstance ?o ?sig }
                 P{ Instance ?c W{ f } }
             } }
          } ==! ] ;

! NOTE: don't use internal optimized implementations here
GENERIC: make-pred-quot ( predicate-word class -- quot )

! { real fixnum array }
! [ dup real? [ nip ] [ dup fixnum? [ nip ] [ array? ] if* ] if* ]
M: union-class make-pred-quot nip
    "members" word-prop <reversed> unclip "predicate" word-prop
    swap
    [ ! ( acc class )
     "predicate" word-prop swap
     '[ dup @ [ nip ] _ if* ]
    ] each ;
M: predicate-class make-pred-quot drop def>> ;

CHR: type-of-predicate @ { TypeOfWord ?w ?tau } // -- [ ?w "predicating" word-prop :>> ?c ]
[ ?c class-not :>> ?d ]
[ ?w ?c make-pred-quot :>> ?p ]
! [ ?c predicate-class? [ ?p keep over [ { ?c } declare drop ] [ { ?d } declare drop ] if ] ?p ? :>> ?q ]
[ [ ?p keep over [ { ?c } declare drop ] [ { ?d } declare drop ] if ] :>> ?q ]
|
{ ?TypeOf ?q ?tau } ;

! : <array> ( n elt -- array )
CHR: type-of-<array> @ { TypeOfWord <array> ?tau } // -- |
[ ?tau
  P{ Effect L{ ?v ?n . ?r } L{ ?a . ?r } { ?v } {
         P{ Instance ?n fixnum }
         P{ Instance ?a array }
         P{ Length ?a ?n }
         P{ Element ?a ?v }
     } }
  ==! ] ;

! : array-nth ( n array -- elt )
! NOTE: existentials
CHR: type-of-access @ { TypeOfWord array-nth ?tau } // -- |
[ ?tau
  P{ Effect L{ ?l ?n . ?a } L{ ?v . ?a } f {
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
  P{ Effect L{ ?m ?o . ?a } L{ ?v . ?a } f {
         P{ Instance ?o not{ fixnum } }
         P{ Instance ?m fixnum }
         P{ Slot ?o ?m ?v }
     } }
  ==! ] ;

! : set-slot ( value obj n -- )
CHR: type-of-set-slot @ { TypeOfWord set-slot ?tau } // -- [ ?tau term-var? ] |
[ ?tau
  P{ Effect L{ ?n ?o ?v . ?a } ?a f {
         P{ Instance ?n fixnum }
         P{ Slot ?o ?n ?v }
     } }
  ==!
] ;

CHR: type-of-throw @ // { ?TypeOf [ throw ] ?tau } -- |
! [ ?tau P{ Effect ?a +bottom+ f } ==! ] ;
! [ ?tau null ==! ] ;
[ ?tau P{ Effect L{ ?e . ?a } ?b f {
              ! P{ Throws ?e }
              P{ Invalid }
          } }
  ==! ] ;

CHR: type-of-boa @ // { ?TypeOf [ boa ] ?tau } -- |
[ ?tau
  P{ Effect L{ ?c . ?a } L{ ?v . ?b } f { P{ Instance ?c tuple-class } P{ Boa ?c ?a L{ ?v . ?b } }
                                          P{ Instance ?v tuple } } }
  ==!
] ;

CHR: type-of-tuple-boa @ // { ?TypeOf [ <tuple-boa> ] ?tau } -- |
[ ?tau
  P{ Effect L{ ?c . ?a } L{ ?v . ?b } f { P{ Instance ?c array } P{ TupleBoa ?c ?a L{ ?v . ?b } }
                                          P{ Instance ?v tuple } } }
  ==!
] ;


! *** Destructure unit type queries
UNION: valid-effect-type Effect Xor ;
UNION: valid-type Effect classoid ;

TUPLE: MaybeHaveFold < chr-pred word quot type target ;

CHR: check-word-fixpoint-type @ { TypeOfWord ?w ?rho } // -- [ ?rho full-type? ] |
{ CheckFixpoint ?w ?rho } ;
CHR: have-type-of-word-call @ { ?TypeOf [ ?w ] ?sig } { TypeOfWord ?w ?rho } // --
! [ ?rho valid-effect-type? ]
[ ?rho full-type? ]
[ ?w 1quotation :>> ?q ]
|
! ! NOTE: resolving recursive phi here with this if possible
! { ComposeType ?rho P{ Effect ?a ?a f f } ?tau }
! { TypeOf ?q ?tau } ;
{ TypeOf ?q ?rho } ;

CHR: type-of-wrapper @ // { ?TypeOf ?q ?tau } --
[ ?q quotation? ]
[ ?q length 1 = ]
[ ?q first wrapper? ]
[ ?q first :>> ?v ]
|
[
    ?tau
    P{ Effect ?a L{ ?x . ?a } f { P{ Instance ?x ?v } } }
    ==!
] ;


CHR: ask-type-of-word-call @ { ?TypeOf [ ?w ] ?tau } // -- [ ?w callable-word? ] [ ?tau term-var? ] |
{ TypeOfWord ?w ?sig } ;

CHR: type-of-unit-val @ { ?TypeOf [ ?v ] ?tau } // -- [ ?v callable-word? not ]
[ ?v 1quotation :>> ?q ] |
{ ?TypeOf ?v ?rho }
{ MakeUnit ?rho ?sig }
{ TypeOf ?q ?sig } ;

CHR: make-unit-simple-type @ // { MakeUnit ?rho ?tau } -- [ { ?rho } first valid-type? ] |
[ ?tau P{ Effect ?a L{ ?x . ?a } f { P{ Instance ?x ?rho } } } ==! ] ;

CHR: make-xor-unit-type @ // { MakeUnit P{ Xor ?x ?y } ?tau } -- |
{ MakeXor ?rho ?sig ?tau }
{ MakeUnit ?x ?rho }
{ MakeUnit ?y ?sig } ;

CHR: type-of-val @ // { ?TypeOf A{ ?v } ?tau } -- [ ?v callable? not ] [ ?v callable-word? not ]
|
[ ?tau W{ W{ ?v } } ==! ] ;

! *** Some Primitives
CHR: type-of-eq @ { TypeOfWord eq? ?tau } // -- |
[ ?tau P{ Xor
          P{ Effect L{ ?x ?x . ?a } L{ ?c . ?a } { ?c } { P{ Instance ?c W{ t } } } }
          P{ Effect L{ ?x ?y . ?a } L{ ?c . ?a } { ?c } { P{ Instance ?c W{ f } } P{ Neq ?x ?y } } }
   } ==! ] ;

CHR: type-of-declare @ { TypeOfWord declare ?tau } // -- |
[ ?tau
  P{ Effect L{ ?l . ?a } ?a f {
         P{ Instance ?l array }
         P{ Declare ?l ?a }
     } }
  ==! ] ;

! : tag ( object -- n )
CHR: type-of-tag @ { TypeOfWord tag ?tau } // -- |
[ ?tau
  P{ Effect L{ ?o . ?a } L{ ?n . ?a } f {
         P{ Instance ?n fixnum }
         P{ Tag ?o ?n }
     } } ==! ]  ;

! bignum>fixnum ( x -- y )
CHR: type-of-bignum>fixnum @ { TypeOfWord bignum>fixnum ?tau } // -- |
[ ?tau
  P{ Effect L{ ?x . ?a } L{ ?y . ?a } f {
         P{ Instance ?x bignum }
         P{ Instance ?y fixnum }
     } }
  ==! ] ;

! CHR: type-of-fixnum+ @ { TypeOfWord fixnum+ ?tau } // -- |
! [ ?tau
!   P{ Effect L{ ?x ?y . ?a } L{ ?z . ?b } { P{ Instance ?x fixnum } P{ Instance ?y fixnum } P{ Use ?x } P{ Use ?y } P{ Instance ?z integer } } }
!   ==!
! ] ;

! shift ( x n -- y )
CHR: type-of-fixnum-shift-fast @ { TypeOfWord fixnum-shift-fast ?tau } // -- |
[ ?tau P{ Effect L{ ?n ?x . ?a } L{ ?y . ?a } f {
              P{ Instance ?n fixnum }
              P{ Instance ?x fixnum }
              P{ Instance ?y fixnum }
              P{ Shift ?y ?x ?n }
          } } ==! ] ;

! *** Math
CHR: type-of-+ @ { TypeOfWord A{ + } ?tau } // -- |
[ ?sig
  P{ Effect L{ ?x ?y . ?a } L{ ?z . ?a } f {
         P{ Instance ?z number }
         P{ Sum ?z ?x ?y }
     } } ==! ]
{ ComposeType P{ Effect ?a ?a f { P{ Ensure { number number } ?a } } } ?sig ?tau } ;

CHR: type-of-* @ { TypeOfWord A{ * } ?tau } // -- |
[ ?sig
  P{ Effect L{ ?x ?y . ?a } L{ ?z . ?a } f {
         P{ Instance ?z number }
         P{ Prod ?z ?x ?y }
     } } ==! ]
{ ComposeType P{ Effect ?a ?a f { P{ Ensure { number number } ?a } } } ?sig ?tau } ;

CHR: type-of-< @ { TypeOfWord A{ < } ?tau } // -- |
[
    ?sig
    P{ Xor
       P{ Effect L{ ?x ?y . ?a } L{ ?z . ?a } { ?z } {
              P{ Instance ?z W{ t } }
              P{ Lt ?y ?x }
              ! P{ Neq ?y ?x }
          } }
        P{ Effect L{ ?x ?y . ?a } L{ ?z . ?a } { ?z } {
               P{ Instance ?z W{ f } }
               P{ Le ?x ?y }
           } }
     }
    ==!
]
{ ComposeType P{ Effect ?a ?a f { P{ Ensure { number number } ?a } } } ?sig ?tau } ;

CHR: type-of-= @ { TypeOfWord A{ = } ?tau } // -- |
[
    ?sig
    P{ Xor
       P{ Effect L{ ?x ?y . ?a } L{ ?z . ?a } { ?z } {
              P{ Instance ?z W{ t } }
              P{ Eq ?x ?y }
          } }
       P{ Effect L{ ?x ?y . ?a } L{ ?z . ?a } { ?z } {
              P{ Instance ?z W{ f } }
              P{ Neq ?y ?x }
          } }
     }
    ==!
]
{ ComposeType P{ Effect ?a ?a f { P{ Ensure { number number } ?a } } } ?sig ?tau } ;

! TODO: output types
! *** Typed words
CHR: type-of-typed-word @ { TypeOfWord A{ ?w } ?tau } // --
[ ?tau term-var? ]
[ ?w "typed-def" word-prop :>> ?q ]
[ ?w "declared-effect" word-prop effect-in-types <reversed> >list :>> ?a ]
|
{ ?TypeOf ?q ?rho }
{ ComposeType P{ Effect ?x ?x f { P{ Declare ?a ?x } } } ?rho ?tau } ;

! *** Other words

CONSTANT: force-compile
{ if }

CHR: type-of-macro @ { TypeOfWord A{ ?w } ?tau } // --
[ ?tau term-var? ]
! [ ?tau macro? ] |
[ ?w "transform-n" word-prop ?w force-compile in? not and ] |
! [ ?w "transform-quot" word-prop :>> ?q ] |
! { ?TypeOf ?q ?rho }
! { ?TypeOf [ call call ] ?sig }
! { ComposeType ?rho ?sig ?tau }
[ ?tau P{ Effect ?a ?b f {
              ! P{ MacroArgs ?w ?a L{ ?q . ?b } }
              P{ MacroCall ?w f ?a ?b }
          } }
==! ]
;

CHR: type-of-regular-word @ { TypeOfWord A{ ?w } ?tau } // --
[ ?tau term-var? ]
[ ?w word-alias not ]
[ ?w method? not ]
[ ?w callable-word? ]
[ ?w "no-compile" word-prop not ]
[ ?w "predicating" word-prop not ]
! [ ?w "transform-quot" word-prop not ]
[ ?w generic? not ]
[ ?w def>> ?w 1quotation = not ]
[ ?w def>> :>> ?q ]
[ ?w "input-classes" word-prop >array :>> ?c ]
|
{ ?TypeOf ?q ?sig }
{ ComposeType P{ Effect ?a ?a f { P{ Ensure ?c ?a } } } ?sig ?tau } ;

! This is actually the one spot where we can declare that things don't overlap
! although they would do if we inferred them as random possible branches of an
! XOR type.  Normally, if parameters overlap, we unionize them to enforce
! XOR-Property, i.e. ensure that actually only one branch can be taken.  Here we
! explicitly encode the not-instance declarations which would be implied during
! runtime dispatch.
! Takes an ordered list of { class method } specs, and modifies it to exclude
! previous ones.
: make-disjoint-classes-step ( not-class next-in -- not-class next-out )
    [ swap class-not simplifying-class-and ]
    [ class-or ] 2bi swap ;

: make-disjoint-classes ( classes -- classes )
    null swap [ make-disjoint-classes-step ] map nip ;

: enforce-dispatch-order ( methods -- methods )
    <reversed> unzip [ make-disjoint-classes ] dip
    zip ;

: dispatch-method-seq ( single-generic -- seq )
    dup "methods" word-prop sort-methods object over key?
    [ nip ]
    [
        [ "default-method" word-prop object swap 2array ] dip swap prefix
    ] if enforce-dispatch-order ;


CHR: type-of-generic @ { TypeOfWord ?w ?tau } // --
[ ?tau term-var? ]
[ ?w single-generic? ]
[ ?w dispatch# :>> ?i ]
[ ?w "transform-quot" word-prop not ]
[ ?w dispatch-method-seq >list :>> ?l ]
[ ?w stack-effect effect>stacks :>> ?b drop :>> ?a ]
|
{ MakeSingleDispatch ?i ?l ?tau } ;

: dispatch-decl ( class num -- seq )
    dup 1 + object <array> [ set-nth ] keep ;

CHR: dispatch-done @ // { MakeSingleDispatch __ +nil+ ?tau } -- | [ ?tau null ==! ] ;
CHR: dispatch-case @ // { MakeSingleDispatch ?i L{ { ?c ?m } . ?r } ?tau } --
[ ?c ?i dispatch-decl <reversed> >list :>> ?l ]
|
{ TypeOfWord ?m ?a }
! TODO: make this a declare quot instead of pred?
! Here we prefix the method word type with the excluded cases from the ordered dispatch
{ ComposeType P{ Effect ?b ?b f { P{ Declare ?l ?b } } } ?a ?rho }
{ MakeSingleDispatch ?i ?r ?sig }
{ MakeXor ?rho ?sig ?d }
{ CheckXor ?m ?d ?tau } ;

CHR: type-of-reader @ { TypeOfWord ?w ?tau } // -- [ ?w method? ] [ ?w "reading" word-prop :>> ?x ]
[ ?w "method-class" word-prop :>> ?c ]
[ ?x class>> :>> ?d ] [ ?x name>> :>> ?n ] |
[ ?tau
  P{ Effect L{ ?o . ?a } L{ ?v . ?a } f
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
{ ComposeType P{ Effect ?a ?a f { P{ Declare ?l ?a } } } ?rho ?tau } ;


CHR: type-of-empty-quot @ // { ?TypeOf [ ] ?tau } -- | [ ?tau P{ Effect ?a ?a f f } ==! ] ;

CHR: type-of-proper-quot @ { ?TypeOf ?q ?tau } // -- [ ?q callable? ] [ ?q length 1 > ]
[ \ do-primitive ?q in? not ]
[ ?q dup length 2 /i cut :>> ?y drop :>> ?x drop t ] |
{ ?TypeOf ?x ?rho }
{ ?TypeOf ?y ?sig }
{ ComposeType ?rho ?sig ?a }
{ CheckXor ?q ?a ?b }
{ TypeOf ?q ?b } ;

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

CHR: compose-effects @ // { ComposeType P{ Effect ?a ?b ?x ?k } P{ Effect ?c ?d ?y ?l } ?tau } --
|
[| |
 P{ Effect ?a ?b ?x ?k } fresh-effect :> e1
 P{ Effect ?c ?d ?y ?l } fresh-effect :> e2
 ! P{ Effect ?a ?b ?k } fresh :> e1
 ! P{ Effect ?c ?d ?l } fresh :> e2
 P{ ComposeEffect e1 e2 ?tau }
] ;

CHR: compose-null-right @ // { ComposeType ?e null ?tau } -- |
[ ?tau null ==! ] ;

CHR: compose-null-left @ // { ComposeType null ?e ?tau } -- |
[ ?tau null ==! ] ;

CHR: compose-xor-effects-right @ // { ComposeType P{ Effect ?a ?b ?z ?k } P{ Xor ?x ?y } ?tau } -- |
{ ComposeType P{ Effect ?a ?b ?z ?k } ?x ?rho }
{ ComposeType P{ Effect ?a ?b ?z ?k } ?y ?sig }
{ MakeXor ?rho ?sig ?tau } ;

CHR: compose-xor-effects-left @ // { ComposeType P{ Xor ?x ?y } P{ Effect ?a ?b ?z ?k } ?tau } -- |
{ ComposeType ?x P{ Effect ?a ?b ?z ?k } ?rho }
{ ComposeType ?y P{ Effect ?a ?b ?z ?k } ?sig }
{ MakeXor ?rho ?sig ?tau } ;


CHR: compose-xor-effects-both @ // { ComposeType P{ Xor ?a ?b } P{ Xor ?c ?d } ?tau } -- |
{ ComposeType ?a P{ Xor ?c ?d } ?rho }
{ ComposeType ?b P{ Xor ?c ?d } ?sig }
{ MakeXor ?rho ?sig ?tau } ;


! NOTE: While kept for reasoning in straight-line composition,
! we don't allow errors into intersection types
CHR: exclude-error-xor-left @ // { MakeXor P{ Effect __ __ __ ?k } ?sig ?tau } -- [ ?k [ Throws? ] any? ] |
{ MakeXor null ?sig ?tau } ;
CHR: exclude-error-xor-right @ // { MakeXor ?rho P{ Effect __ __ __ ?k } ?tau } -- [ ?k [ Throws? ] any? ] |
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

! The question is how to decide which XOR's to keep.  Going bottom-up, pretty much
! every conditional and/or type test defines two branches.  So for any composition
! of words, the worst-case is a 2^n blow-up in the word length n of branches.
! The reason to keep separate branches of the intersection types in the first
! place is that we want to keep around enough information to exclude stuff during
! composition: If we define a generic function with several methods on disjoint
! data-types, the information loss of actually lumping everything together into
! union classes is comparatively large.  The following cases seem to be
! interesting:

! 1. Depending on disjoint input types, the word defines disjoint output types.
!    This is e.g. a use case where we have separate implementations of say a
!    mapper function.  If we run a mapping operation, we want to be able to
!    transport these dependencies into the Sequence-Of parametric types

! Problem with not having explicit bind/dup operations anymore:
! two effects like ~( x y -- y x )~ and maybe ~( a x -- b x )~ represent different
! kinds of data shuffling (in addition to whatever predicates they have).  For phi
! operations, the general approach is:
! 1. Assume the same input data for stuff
! 2. Run stuff through effect1
! 3. Run stuff through effect2
! 4. Perform union-reasoning on the predicates, collect results.

! Normally, assuming the same input data for stuff means performing unification.
! However there seems to be a problem with that.

! The first effect (~swap~) could also be expressed with explicit bind/dup predicates, e.g.
! ~( x1 y1 -- y2 x2 )~ where ~y2: y1~, and ~x2: x1~.   This means, that an effect
! which does not use explicit var-copying but a single variable for input and
! output var actually "hides" an additional equality constraint between input and
! output.

! Using the "explicit discriminator" approach, we would normally define the member
! s of a relation induced by an equality predicate as parameters of the type.
! I.e. the ~swap~ word would then considered to be a predicate class on a stack
! whose top two elements on output depend on the top two elements on input:


! Forall x, y: (..ρ, x, y) → (..ρ, y, x)

TUPLE: PhiSchedule < chr-pred quot list target ;
TUPLE: DisjointRoot < chr-pred effect ;
TUPLE: DestrucXor < chr-pred branch ;
TUPLE: RebuildXor < chr-pred effect target ;
TUPLE: CurrentPhi < chr-pred effect ;
TUPLE: MakeUnion < chr-pred effect1 effect2 target ;
TUPLE: IsUnion < chr-pred pred ;
! Marker to switch reasoning to assume disjunction of value info
TUPLE: PhiMode < chr-pred ;

! Marker to force disjunction of value info
TUPLE: FixpointMode < chr-pred ;
TUPLE: PhiDone < chr-pred ;
! Used during phi reasoning to distinguish regular ids from
! possible parametric-type-defining ones
! TUPLE: Discrims < chr-pred vars ;
! Catch
CHR: maybe-make-trivial-xor @ // { MakeXor ?rho ?sig ?tau } -- [ ?rho full-type? ] [ ?sig full-type? ] |
[ ?rho ?sig isomorphic?
  [ ?tau ?rho ==! ]
  [ ?tau P{ Xor ?rho ?sig } ==! ]
  ! { CheckXor ?rho ?sig ?tau }
  ?
] ;

! Some sanity checks
! CHR: xor-error @ <={ CheckXor } <={ CheckXor } // -- | [ "xor sequencing error" throw ] ;
CHR: phi-error @ <={ PhiSchedule } <={ PhiSchedule } // -- | [ "phi sequencing error" throw ] ;
CHR: current-phi-error @ { CurrentPhi __ } { CurrentPhi __ } // -- | [ "current phi sequencing error" throw ] ;
CHR: make-union-error @ <={ MakeUnion } <={ MakeUnion } // -- | [ "double make-union" throw ] ;

! CHR: also-check-fixpoint @ { CheckXor ?q ?rho ?tau } // -- [ ?rho full-type? ] |
! { CheckFixpoint ?q ?rho } ;
! Start Destructuring, trigger schedule
CHR: no-check-xor @ // { CheckXor __ ?rho ?tau } -- [ ?rho full-type? ] [ ?rho Effect? ] |
! CHR: no-check-xor @ // { CheckXor ?rho ?tau } -- [ ?rho full-type? ] |
[ ?rho ?tau ==! ] ;

! If we inferred an effect type to be null, then substitute it with a null-push that will
! cause exclusion of this effect from further Xor reasonings.
! TODO TBR?
CHR: check-xor-null-throws @ // { CheckXor ?q null ?tau } -- [ ?tau term-var? ] |
[ ?tau P{ Effect ?a L{ ?x . ?a } { } { P{ Instance ?x null } } } ==! ] ;

CHR: do-check-xor @ // { CheckXor ?q ?rho ?tau } -- [ ?rho full-type? ] |
{ DestrucXor ?rho }
{ PhiSchedule ?q +nil+ ?tau } ;

PREDICATE: InvalidEffect < Effect preds>> [ Invalid? ] any? ;

CHR: discard-invalid-branch @ // { DestrucXor ?e } -- [ ?e InvalidEffect? ] | ;
CHR: destruc-rebuild-xor @ // { DestrucXor P{ Xor ?a ?b } } -- |
{ DestrucXor ?a } { DestrucXor ?b } ;
CHR: destruc-rebuild-effect @ // { PhiSchedule ?q ?r ?tau } { DestrucXor ?e } -- [ ?e Effect? ] |
{ PhiSchedule ?q L{ ?e . ?r } ?tau } ;

! Triggers actual phi-reasoning
! NOTE: To avoid things like ~[ swap ] when~ to unify the vars,
! the (unknown) vars themselves have to be treated as the types.  So this means that if we meet
! e.g. two effects ~( x y -- y x ) ( a b -- a b )~, we first need to unify the inputs, and then check
! if we can still unify the whole effect.

CHR: try-next-phi @ { CurrentPhi ?a } P{ PhiSchedule __ L{ ?b . ?r } __ } // -- |
[| |
 ?a fresh-effect :> e1
 ?b fresh-effect :> e2
 { P{ MakeUnion e1 e2 ?tau } } ] ;

! Finished force-union schedule
CHR: all-fixpoint-phis-done @ // { PhiSchedule __ +nil+ ?tau } { FixpointMode } { DisjointRoot ?a } -- |
[ ?a Xor? [ ?a "not a straightline-effect" 2array throw ] [ f ] if ]
[ ?tau ?a ==! ] ;

! Finished Schedules
CHR: all-phis-done @ { PhiSchedule __ +nil+ ?tau } // { DisjointRoot ?a } -- |
{ RebuildXor ?a ?tau } ;

:: alpha-equiv-under? ( t1 t2 bound -- subst/f )
    t1 vars t2 vars union bound diff valid-match-vars
    [ t1 t2 solve-eq ] with-variable ;

! *** Rebuild two effects as union
! CHR: check-non-unionable-effect @ { MakeUnion P{ Effect ?a ?b ?x ?l } P{ Effect ?a ?d ?y ?k } ?tau } // -- [ ?tau term-var? ] |
! [
!     ?b ?d ?a vars alpha-equiv-under? not
!     { [ ?tau null ==! ] P{ PhiDone } } f ?
!  ] ;

! Trigger Phi-mode Composition
! This causes the reasoner to assume disjunction instead of conjunction of value predicates.
CHR: try-union-effect @ { MakeUnion ?a ?b ?tau } // -- [ ?tau term-var? ] |
{ PhiMode }
{ ComposeEffect ?a ?b ?tau } ;

! After MakeEffect has finished
CHR: have-union-effect @ // { DisjointRoot ?e } { CurrentPhi ?e } { MakeUnion __ __ ?a } { PhiDone } { PhiSchedule ?q L{ ?b . ?r } ?tau } --
[ ?a Effect? ] | { DisjointRoot ?a } { PhiSchedule ?q ?r ?tau } ;

CHR: have-disjoint-effect @ // { CurrentPhi ?e } { MakeUnion __ __ null } { PhiDone } -- | ;

CHR: try-next-phi-merge @ { DisjointRoot ?e } { PhiSchedule __ L{ ?b . ?r } __ } // -- | { CurrentPhi ?e } ;

CHR: no-next-phi-merge @ // { PhiSchedule ?q L{ ?b . ?r } ?tau } -- |
{ DisjointRoot ?b } { PhiSchedule ?q ?r ?tau } ;

! *** Rebuild after intersection checking
CHR: rebuild-phi-collect-branch @ { PhiSchedule ?q +nil+ ?tau } // { RebuildXor ?a ?tau } { DisjointRoot ?b } -- |
{ RebuildXor P{ Xor ?b ?a } ?tau } ;

CHR: rebuild-phi-finished @ // { PhiSchedule ?q +nil+ ?tau } { RebuildXor ?a ?tau } -- |
[ ?tau ?a ==! ] ;

! *** Build Fixpoint type
: has-recursive-call? ( tag Effect -- ? )
    preds>> [ dup CallRecursive? [ tag>> = ] [ 2drop f ] if ] with any? ;
: filter-recursive-call ( tag Effect -- Effect )
    clone
    [ [ dup CallRecursive? [ tag>> = ] [ 2drop f ] if ] with reject ] with change-preds ;
GENERIC#: recursive-branches? 1 ( type word/quot -- ? )
M: Effect recursive-branches? swap has-recursive-call? ;
M: Xor recursive-branches? [ [ type1>> ] [ type2>> ] bi ] dip '[ _ recursive-branches? ] either? ;
GENERIC#: terminating-branches 1 ( type word/quot -- branches )
M: Effect terminating-branches over has-recursive-call? [ drop f ] [ 1array ] if ;
M: Xor terminating-branches [ [ type1>> ] [ type2>> ] bi ] dip '[ _ terminating-branches ] bi@ append sift ;
GENERIC#: recursive-branches 1 ( type word/quot -- branches )
M: Effect recursive-branches over has-recursive-call? [ 1array ] [ drop f ] if ;
M: Xor recursive-branches [ [ type1>> ] [ type2>> ] bi ] dip '[ _ recursive-branches ] bi@ append sift ;
CHR: no-check-fixpoint @ // { CheckFixpoint ?q ?rho } -- [ ?rho ?q recursive-branches? not ] | ;
CHR: do-check-fixpoint @ // { CheckFixpoint ?q ?rho } -- [ ?rho ?q terminating-branches :>> ?l drop t ]
[ ?rho ?q recursive-branches :>> ?k drop t ] |
[| |
    ?l [ f ] [
        >list :> fp-phis
        {
            ! P{ FixpointMode }
            P{ PhiSchedule ?q fp-phis ?tau }
            P{ FixpointTypeOf ?q ?tau }
        }
    ] if-empty
    ?k [ f ] [
        ! [ ?q swap filter-recursive-call ] map
        >list :> rec-phis
        {
            P{ FixpointMode }
            P{ PhiSchedule ?q rec-phis ?sig }
            P{ RecursionTypeOf ?q ?sig }
        }
    ] if-empty append
] ;

! ** Simplification/Intra-Effect reasoning
IMPORT: chr-phi
UNION: body-pred Instance NotInstance CallEffect Declare Slot CallRecursive Throws Tag
    NullStack MacroCall expr-pred Iterated ;
TUPLE: Params < chr-pred ids ;
TUPLE: Param < chr-pred id ;

CHR: invalid-stays-invalid @ { Invalid } // { Invalid } -- | ;


! *** Normalizations
UNION: commutative-pred Eq Neq ;
CHR: comm-var-is-lhs @ // AS: ?p <={ commutative-pred A{ ?l } ?v } -- [ ?v term-var? ] |
[ { ?v ?l } ?p class-of slots>tuple ] ;

CHR: singleton-class-is-literal @ // { Instance ?x ?tau } -- [ { ?tau } first wrapper? not ] [ ?tau singleton-class? ] |
{ Instance ?x W{ ?tau } } ;

! *** Start unification reasoning
! NOTE: assumed renaming here already
CHR: rebuild-phi-effect @ { PhiMode } // { ComposeEffect P{ Effect ?a ?b ?x ?k } P{ Effect ?c ?d ?y ?l } ?tau } --
[ { ?a ?b } { ?c ?d } unify drop t ]
|
! NOTE: This happens if we have pre-defined effects but no known body yet (e.g. recursive calls)
! [ ?k dup term-var? [ drop f ] when ]
! [ ?l dup term-var? [ drop f ] when ]
! [ { ?x ?y } [ f lift ] no-var-restrictions first2 intersect Params boa ]
! [ ?x ?y union Params boa ]
{ PhiStack ?v ?a }
{ PhiStack ?v ?c }
{ PhiStack ?w ?b }
{ PhiStack ?w ?d }
{ Params { } }
[ ?x [ Param boa ] map ]
[ ?y [ Param boa ] map ]
[ ?k ]
[ ?l ]
{ MakeEffect ?v ?w f f ?tau } ;

CHR: rebuild-compose-effect @ // { ComposeEffect P{ Effect ?a ?b ?x ?k } P{ Effect ?c ?d ?y ?l } ?tau } -- |
[ ?b ?c ==! ]
! NOTE: This happens if we have pre-defined effects but no known body yet (e.g. recursive calls)
! [ ?k dup term-var? [ drop f ] when ]
! [ ?l dup term-var? [ drop f ] when ]
{ Params ?x }
{ Params ?y }
[ ?k ]
[ ?l ]
{ MakeEffect ?a ?d f f ?tau } ;

CHR: force-union @ { PhiMode } { FixpointMode } // { Invalid } -- | ;

CHR: early-exit @ { Invalid } // <={ body-pred } -- | ;

! *** <Phi
! ! **** Discarding nested calls for recursion types
! CHR: clear-rec-type-rec-call @ { PhiMode } { FixpointMode } { PhiSchedule ?w __ __ } // { CallRecursive ?w __ __ } -- | ;

! CHR: invalid-union @ { Invalid } // { IsUnion __ } -- | ;

! **** Re-building identities
! NOTE: the only way how two of these can be present at the same time is if both effects specify
! the same bind after stack unification
! CHR: both-bind-same-var @ { PhiMode } // { Bind ?y ?x } { Bind ?y ?x } -- | [ ?y ?x ==! ] ;

! UNION: bound-propagated-preds Instance expr-pred ;
! CHR: propagate-bound-pred @ { PhiMode } { Bind ?y ?x } AS: ?p <={ bound-propagated-preds ?x . __ } // -- |
! [ ?p clone ?y >>val ] ;

! CHR: same-stays-valid @ { Phi ?z ?x } { Phi ?z ?y } // AS: ?p <={ val-pred ?x . ?xs } AS: ?q <={ val-pred ?y . ?xs } -- [ ?p ?q [ class-of ] same? ] |
! [ ?p clone ?z >>val ] ;
! **** Phi Parameter Handling
! CHR: phi-single-parm @ { PhiMode } // { Params ?l } -- | [ ?l [ Param boa ] map ] ;
CHR: phi-parm-intersect @ { Phi ?z ?x } { Phi ?z ?y } // { Param ?x } { Param ?y } -- | { Params { ?z } } ;
! CHR: phi-merge-params @ // { IsUnion P{ Params ?l } } { IsUnion P{ Params ?k } } -- [ ?l ?k union :>> ?m ] |
! { IsUnion P{ Params ?m } } ;
! CHR: phi-no-param @ // { Param __ } -- | ;


! NOTE: this is pretty tricky with regards to what constitutes valid criteria for /not/
! merging types during phi reasoning.  Couple of approaches:
! 1. Any joined type, be it input, internal, or output is considered to be in covariant position
! 2. Only output types are considered to be in covariant position
! 3. Some explicit dependency type magic determines under what conditions we want to be distinct...
CHR: phi-disjoint-instance @ { Phi ?z ?x } { Phi ?z ?y } { Params ?l } // { Instance ?x A{ ?rho } } { Instance ?y A{ ?tau } } --
[ ?z ?l in? ] [ { ?rho ?tau } first2 classes-intersect? not ] | { Invalid } ;

! ! ( x <= 5 ) ( 5 <= x ) -> union
! ! ( x <= 4 ) ( 5 <= x ) -> disjoint
! ! ( x <= 5 ) ( 4 <= x ) -> union
! CHR: phi-disjoint-output-range-le-le @ { PhiMode } // { Le ?x A{ ?m } } { Le A{ ?n } ?x } --
! [ ?m ?n < ] | { Invalid } ;
! ! ( x < 5 ) ( 5 <= x ) -> disjoint
! ! ( x < 4 ) ( 5 <= x ) -> disjoint
! ! ( x < 5 ) ( 4 <= x ) -> union
! CHR: phi-disjoint-output-range-lt-le @ { PhiMode } // { Lt ?x A{ ?m } } { Le A{ ?n } ?x } --
! [ ?m ?n <= ] | { Invalid } ;
! CHR: phi-disjoint-output-range-le-lt @ { PhiMode } // { Le ?x A{ ?m } } { Lt A{ ?n } ?x } --
! [ ?m ?n <= ] | { Invalid } ;
! ! ( x < 5 ) ( 5 < x ) -> disjoint
! ! ( x < 4 ) ( 5 < x ) -> disjoint
! ! ( x < 5 ) ( 4 < x ) -> union
! CHR: phi-disjoint-output-range-lt-lt @ { PhiMode } // { Le ?x A{ ?m } } { Lt A{ ?n } ?x } --
! [ ?m ?n <= ] | { Invalid } ;
! CHR: phi-disjoint-output-range-lt-eq @ { PhiMode } // { Eq ?x A{ ?n } } { Lt ?x A{ ?n } } -- | { Invalid } ;

! TODO: this is not recursive!
! NOTE: Rationale: An effect type is refined by its body predicates, which act as set subtraction.
! So the more general type is the one which has body predicates that both must agree on.
! If they have the same set of parameters but different bodies, they define a dependent type.
! CHR: phi-phiable-effect-instance @ { PhiMode } // { Instance ?x P{ Effect ?a ?b ?r ?k } } { Instance ?x P{ Effect ?c ?d ?s ?l } } --
! [ ?r empty? ] [ ?s empty? ]
! [ { ?a ?b } { ?c ?d } unify ] |
! [ { ?a ?b } { ?c ?d } ==! ]
! [| | ?l ?k intersect :> body
!  P{ IsUnion P{ Instance ?x P{ Effect ?a ?b f body } } }
! ] ;
! **** phi union types
CHR: phi-instance @ { Phi ?z ?x } { Phi ?z ?y } // { Instance ?x A{ ?rho } } { Instance ?y A{ ?sig } } --
[ { ?rho ?sig } first2 class-or :>> ?tau ] |
{ Instance ?z ?tau } ;

! Slots
CHR: phi-slot @ { Phi ?z ?x } { Phi ?z ?y } // { Slot ?x ?n ?a } { Slot ?y ?n ?b } -- |
{ Phi ?c ?a } { Phi ?c ?b } { Slot ?z ?n ?c } ;

! **** phi higher order

CHR: phi-call-effect-match-in @ { Phi ?r ?p } { Phi ?r ?q }
// { CallEffect ?p ?a ?b } { CallEffect ?q ?x ?y } -- |
{ PhiStack ?v ?a }
{ PhiStack ?v ?x }
{ PhiStack ?w ?b }
{ PhiStack ?w ?y }
{ CallEffect ?r ?v ?w } ;

! TODO: make this dependent on whether we simplify our own def!
! CHR: phi-call-rec-match @ { Phi ?r ?p } { Phi ?r ?q }
! // { CallRecursive ?w ?a ?b } { CallRecursive ?w ?x ?y } --
! { ?Phi ?v ?a ?x ?l }
! { ?Phi ?z ?b ?y ?l }
! |
! [ ?k Yes == ?l Yes == and
!   {
!       P{ PhiStack ?z ?a }
!       P{ PhiStack ?z ?x }
!       P{ CallRecursive ?w ?v ?z }
!   }
!   P{ Invalid } ?
! ] ;

! **** phi recursive calls

! We don't merge call-recursives for our own disjoint definition
CHR: phi-call-rec-self @ { PhiMode } { PhiSchedule ?w __ __ } //
{ CallRecursive ?w __ __ } -- | { Invalid } ;

! CHR: phi-call-rec-have-type @ { PhiMode } { FixpointTypeOf ?w ?e } // { CallRecursive ?w ?a ?b } -- [ ?e full-type? ] |
! [ { ?a ?b } { ?c ?d } ==! ]
! { Params ?x }
! [ ?l ] ;
! [| | ?e fresh-effect { [ in>> ] [ out>> ] [ parms>> ] [ preds>> ] } cleave
!  :> ( in out parms preds )
!  {
!      [ { ?a ?b } ]
!  }
! ]

! **** Conditions under which even a single pred can conserve disjunctivity
! CHR: disj-output-maybe-callable @ { PhiMode } { MakeEffect __ ?b __ __ __ } // { Instance ?x A{ ?tau } } --
! [ ?x ?b vars in? ] [ { ?tau } first classoid? ] [ { ?tau } first callable classes-intersect? ] | { Invalid } ;

! CHR: disj-param-maybe-callable @ { PhiMode } <={ MakeEffect } { Params ?l } // { Instance ?x A{ ?tau } } --
! [ ?x ?l in? ] [ { ?tau } first classoid? ] [ { ?tau } first callable classes-intersect? ] | { Invalid } ;

CHR: disj-is-macro-effect @ { PhiMode } <={ MakeEffect } // <={ MacroCall } -- | { Invalid } ;

! CHR: disj-is-inline-effect @ { PhiMode } <={ MakeEffect } { Phi ?r ?p } // <={ CallEffect ?p . __ } -- | { Invalid } ;

! Unknown call-rec
CHR: disj-single-call-rec @ { PhiMode } <={ MakeEffect } // <={ CallRecursive } -- | { Invalid } ;

! CHR: disj-single-effect @ { PhiMode } <={ MakeEffect } // { Instance ?x P{ Effect __ __ __ __ } } -- | { Invalid } ;

! TODO: does that reasoning work? Basically, we would need to have absence as failure here...
! CHR: disj-unknown-can-be-callable @ { PhiMode } <={ MakeEffect } // { Instance ?x A{ ?tau } }

CHR: disj-symbolic-type @ { PhiMode } <={ MakeEffect } { Params ?b } // { Instance ?x ?tau } -- [ ?tau term-var? ] [ ?x ?b in? ] | { Invalid } ;
CHR: disj-symbolic-compl-type @ { PhiMode } <={ MakeEffect } { Params ?b } // { NotInstance ?x ?tau } -- [ ?tau term-var? ] [ ?x ?b in? ] | { Invalid } ;

! *** Phi>

! TODO: extend to other body preds
CHR: unique-instance @ { Instance ?x ?tau } // { Instance ?x ?tau } -- | ;

CHR: uniqe-slot @ { Slot ?o ?n ?v } // { Slot ?o ?n ?v } -- | ;

CHR: merge-params @ // { Params ?x } { Params ?y } -- [ ?x ?y union >array :>> ?z ] | { Params ?z } ;

! NOTE: the reasoning is that this can inductively only happen during composition of two straight-line
! effects. So the instance in the first one is a "provide", and the instance in the second one is an "expect".
! Since the intersection type operation is commutative, we don't care which came from which.
CHR: same-slot-must-be-same-var @ { Slot ?o ?n ?v } // { Slot ?o ?n ?w } -- | [ ?v ?w ==! ] ;

: typeof>tag ( quoted -- n/f )
    first
    {
        { [ dup wrapper? ] [ wrapped>> tag ] }
        { [ dup tuple-class? ] [ drop tuple class>type ] }
        { [ dup class? ] [ class>type ] }
        [ drop f ]
    } cond ;

! *** Instance reasoning
CHR: check-tag @ { Instance ?x A{ ?v } } // { Tag ?x A{ ?n } } -- [ { ?v } typeof>tag :>> ?m ] |
[ ?m ?n = f { Invalid } ? ] ;

CHR: literal-defines-tag @ { Instance ?x A{ ?v } } { Tag ?x ?n } // -- [ { ?v } typeof>tag :>> ?m ]
[ ?v tag :>> ?m ] | { Instance ?n W{ ?m } } ;

CHR: convert-tag @ // { Tag ?x A{ ?n } } -- [ ?n type>class :>> ?tau ] |
{ Instance ?x ?tau } ;

! CHR: useless-instance @ // { Instance __ object } -- | ;
CHR: null-instance-is-invalid @ { Instance ?x null } // -- | { Invalid } ;

CHR: normalize-not-type @ // { NotInstance ?x A{ ?tau } } -- [ { ?tau } first classoid? ]
[ { ?tau } first class-not :>> ?sig ] |
{ Instance ?x ?sig } ;

CHR: type-contradiction @ // { NotInstance ?x ?tau } { Instance ?x ?tau } -- | { Invalid } ;

! NOTE: There are two ways to handle intersections: in factor's type system in
! the intersection instance type, or in the
! implicit conjunction of the constraint store.  Currently, this is put into the
! intersection classes of the factor type system.
CHR: instance-intersection @
// { Instance ?x A{ ?tau } } { Instance ?x A{ ?sig } } --
[ { ?tau ?sig } first2 simplifying-class-and :>> ?c ] |
{ Instance ?x ?c } ;

CHR: instance-intersect-effect @ { Instance ?x ?e }
// { Instance ?x A{ ?tau } } --
[ ?e valid-effect-type? ] |
[ ?tau callable eq? ?tau quotation eq? or
 f { Invalid } ? ] ;

! TODO: used? looks like should be subsumed by null-instance-is-invalid
CHR: call-null-instance-is-invalid @ { CallEffect ?x __ __ } { Instance ?x null } // -- | { Invalid } ;

! *** Macro Expansion/Folding
! NOTE: destructive
CHR: adjust-macro-stack @ // { MacroCall ?w f ?a ?b } -- [ ?w word? ] [ ?w "transform-n" word-prop :>> ?n ]
[ ?w "transform-quot" word-prop :>> ?q ] |
[| |
 ?n "v" utermvar <array> :> mparms
 mparms <reversed> >list ?rho lappend :> sin
 {
     [ ?a sin ==! ]
     { MacroCall ?q mparms sin ?b }
 }
] ;

! *** Arithmetics
CHR: unique-expr-pred @ AS: ?p <={ expr-pred ?a . ?x } // AS: ?q <={ expr-pred ?a . ?x } -- [ ?p class-of ?q class-of class= ] | ;

CHR: check-le @ // { Le A{ ?x } A{ ?y } } -- [ ?x ?y <= not ] | { Invalid } ;
CHR: check-le-same @ // { Le ?x ?x } -- | ;
CHR: check-lt @ // { Lt A{ ?x } A{ ?y } } -- [ ?x ?y < not ] | { Invalid } ;
CHR: lt-tightens-le @ { Lt ?x ?y } // { Le ?x ?y } -- | ;
CHR: le-defines-eq @ // { Le ?x ?y } { Le ?y ?x } -- | { Eq ?x ?y } ;
CHR: lt-defines-neq @ // { Lt ?x ?y } { Lt ?y ?x } -- | { Neq ?x ?y } ;
! CHR: check-lt-1 @ // { Lt ?x ?y } { Lt ?y ?x } -- | { Invalid } ;
CHR: check-lt-same @ // { Lt ?x ?x } -- | { Invalid } ;
CHR: check-lt-eq-1 @ // { Lt ?x ?y } { Eq ?x ?y } -- | { Invalid } ;
CHR: check-lt-eq-2 @ // { Lt ?x ?y } { Eq ?y ?x } -- | { Invalid } ;
CHR: check-eq-1 @ // { Eq ?x ?y } { Neq ?x ?y } -- | { Invalid } ;
CHR: check-eq-2 @ // { Eq ?x ?y } { Neq ?y ?x } -- | { Invalid } ;
CHR: check-neq @ // { Neq A{ ?x } A{ ?y } } -- [ ?x ?y == ] | { Invalid } ;
! Being not equal to something we can't be anyway is redundant
CHR: redundant-neq @ { Instance ?x ?c } // { Neq ?x A{ ?l } } --
[ { ?l } first ?c instance? not ] | ;

CHR: check-sum @ // { Sum A{ ?z } A{ ?x } A{ ?y } } -- [ ?x ?y + ?z = not ] | P{ Invalid } ;
! CHR: zero-sum-1 @ // { Sum ?z 0 ?y } -- | [ ?z ?y ==! ] ;
! CHR: zero-sum-2 @ // { Sum ?z ?x 0 } -- | [ ?z ?x ==! ] ;
CHR: define-sum @ // { Sum ?z A{ ?x } A{ ?y } } --
[ ?x ?y + <wrapper> :>> ?v ] | { Instance ?z ?v } ;
CHR: normalize-sum @ // { Sum ?z A{ ?x } ?y } -- | { Sum ?z ?y ?x } ;

CHR: check-prod @ // { Prod A{ ?z } A{ ?x } A{ ?y } } -- [ ?x ?y * ?z = not ] | P{ Invalid } ;
CHR: neutral-prod-1 @ // { Prod ?z 1 ?y } -- | [ ?z ?y ==! ] ;
CHR: neutral-prod-2 @ // { Prod ?z ?x 1 } -- | [ ?z ?x ==! ] ;
CHR: zero-prod-1 @ // { Prod ?z 0 ?y } -- | { Instance ?z 0 } ;
CHR: zero-prod-2 @ // { Prod ?z ?y 0 } -- | { Instance ?z 0 } ;
CHR: define-prod @ // { Prod ?z A{ ?x } A{ ?y } } --
[ ?x ?y * <wrapper> :>> ?v ] | { Instance ?z ?v } ;

CHR: check-shift @ // { Shift A{ ?z } A{ ?x } A{ ?n } } -- [ ?x ?n shift ?z = not ] | P{ Invalid } ;
CHR: neutral-shift @ // { Shift ?z ?x 0 } -- | [ ?z ?x ==! ] ;
CHR: zero-shift @ // { Shift ?z 0 ?x } -- | { Instance ?z W{ 0 } } ;
CHR: define-shift @ // { Shift ?z A{ ?x } A{ ?n } } --
[ ?x ?n shift <wrapper> :>> ?v ] | { Instance ?z ?v } ;

CHR: check-bitand @ // { BitAnd A{ ?z } A{ ?x } A{ ?y } } -- [ ?x ?y bitand ?z = not ] | { Invalid } ;
CHR: zero-bitand-1 @ // { BitAnd ?z 0 ?y } -- | { Instance ?z W{ 0 } } ;
CHR: zero-bitand-2 @ // { BitAnd ?z ?x 0 } -- | { Instance ?z W{ 0 } } ;
CHR: neutral-bitand-1 @ // { BitAnd ?z -1 ?y } -- | [ ?z ?y ==! ] ;
CHR: neutral-bitand-2 @ // { BitAnd ?z ?x -1 } -- | [ ?z ?x ==! ] ;

! CHR: propagate-lt-offset @ { Lt A{ ?n } ?x } { Sum ?z ?x A{ ?y } } // --
! [ ?n ?y + :>> ?m ] | { Lt ?m ?z } ;
! CHR: propagate-lt-offset @ { Lt ?n ?x } { Sum ?z ?x ?y } // -- |
! { Sum ?w ?n ?y } { Lt ?z ?w } ;

! *** Call Effect matching
! NOTE: These only meet in renamed form?
! NOTE: not sure this has to be restricted to literals, actually, but it feels like we would
! violate the unknown-call safety net...
CHR: call-applies-effect @ { Instance ?q P{ Effect ?c ?d ?x ?l } } { CallEffect ?q ?a ?b } // -- |
[ { ?a ?b } { ?c ?d } ==! ]
{ Params ?x }
[ ?l ] ;

! ! NOTE: Idea: create an iteration constraint.  Should only be active in subsequent compositions
! CHR: call-recursive-iteration @ { RecursionTypeOf ?w ?tau } { FixpointTypeOf ?w ?rho } // { CallRecursive ?w ?a ?b } --
! [ ?tau full-type? ] [ ?rho full-type? ] |
! [| | ?tau fresh-effect [ in>> ] [ out>> ] [ preds>> ] tri :> ( inext onext pnext )
!  ?rho fresh-effect [ in>> ] [ out>> ] [ preds>> ] tri :> ( ilast olast plast )
!  {
!      [ ?b olast ==! ]
!      P{ Iterated ?a inext ilast }
!  } pnext append plast append
! ] ;


! NOTE: we don't apply the inputs here, so we should have the effect of a Kleene star for an unknown number of
! Iterations.  The predicates relating to the inputs of the union type should then be discarded.
! CHR: call-recursive-applies-fixpoint-effect @ { FixpointTypeOf ?w ?e } // { CallRecursive ?w ?a ?b } -- [ ?e full-type? ] |
! [| | ?e fresh-effect { [ in>> ] [ out>> ] [ parms>> ] [ preds>> ] } cleave
!  :> ( in out parms preds )
!  preds out ?b [ solve-eq lift ] no-var-restrictions
!  ! {
!  !     ! [ { ?a ?b } { in out } ==! ]
!  !     ! [ ?b out ==! ]
!  !     ! P{ Params parms }
!  ! }
!  ! preds append
! ] ;

CHR: call-destructs-curry @ { Instance ?q curried } { Slot ?q "quot" ?p } { Slot ?q "obj" ?x } // { CallEffect ?q ?a ?b } -- |
{ CallEffect ?p L{ ?x . ?a } ?b } ;

CHR: call-destructs-composed @ { Instance ?p composed } { Slot ?p "first" ?q } { Slot ?p "second" ?r } // { CallEffect ?p ?a ?b } -- |
{ CallEffect ?q ?a ?rho } { CallEffect ?r ?rho ?b } ;

! *** Declarations

CHR: did-ensure @ // { Ensure +nil+ __ } -- | ;
CHR: did-declare @ // { Declare +nil+ __ } -- | ;
CHR: start-ensure @ // { Ensure A{ ?a } ?r } -- [ ?a array? ]
[ ?a <reversed> >list :>> ?b ] | { Ensure ?b ?r } ;
CHR: destruc-ensure @ // { Ensure L{ ?tau . ?r } L{ ?x . ?xs } } -- |
! { Ensure ?tau ?x }
{ Instance ?x ?tau }
{ Ensure ?r ?xs } ;
! NOTE: destructive!
CHR: ensure-stack @ { Ensure L{ ?tau . ?r } ?x } // -- [ ?x term-var? ] |
[ ?x L{ ?y . ?ys } ==! ] ;
! NOTE: destructive!
CHR: declare-ensures @ { Declare L{ ?tau . ?r } ?x } // -- |
{ Ensure L{ ?tau . ?r } ?x } ;
CHR: destruc-declare @ // { Declare L{ ?tau . ?r } L{ ?x . ?xs } } -- |
{ Params { ?x } }
{ Declare ?r ?xs } ;

! UNION: abstract-class union-class predicate-class ;
! CHR: apply-predicate-ensure @ { Ensure A{ ?tau } ?x } // -- [ ?x term-var? ] [ ?tau abstract-class? ] |
! { Instance ?x ?tau } ;
! CHR: apply-ensure @ // { Ensure A{ ?tau } ?x } -- [ ?x term-var? ] [ ?tau abstract-class? not ] |
! { Instance ?x ?tau } ;

! *** Substituting ground values into body constraints

CHR: known-declare @
! NOTE: for some reason, we can't match into W{ ?v } objects correctly...
{ Instance ?l A{ ?tau } } // { Declare ?l ?a } --
[ { ?tau } first wrapper? ]
[ ?tau <reversed> >list :>> ?m ] | { Declare ?m ?a } ;

! CHR: do-macro @ { Instance ?x ?v }

CHR: known-macro-arg @ { Instance ?x ?v } // { MacroCall ?q ?a ?i ?o } -- [ ?x ?a in? ] [ { ?v } first wrapper? ]
[ { ?v } first wrapped>> :>> ?z ]
|
[| | ?a H{ { ?x ?z } } lift* :> args
 { MacroCall ?q args ?i ?o }
] ;


! CHR: constant-ensure @ // { Ensure ?l ?a } -- [ ?l array? ]
! [ ?l <reversed> >list :>> ?m ] |
! { Ensure ?m ?a } ;

CHR: known-slot @ { Instance ?n A{ ?tau } } // { Slot ?o ?n ?v } -- |
{ Slot ?o ?tau ?v } ;

CHR: known-instance @ { Instance ?c A{ ?tau } } // { Instance ?x ?c } --
[ { ?tau } first wrapped>> :>> ?d ] | { Instance ?x ?d } ;
CHR: known-not-instance @ { Instance ?c A{ ?tau } } // { NotInstance ?x ?c } --
[ { ?tau } first wrapped>> :>> ?d ] | { NotInstance ?x ?d } ;

CHR: known-tag-num @ { Instance ?n A{ ?v } } // { Tag ?c ?n } -- [ { ?v } first wrapper? ] [ ?v :>> ?w ] |
{ Tag ?c ?w } ;


! NOTE: this is still a bit tedious...Maybe we can have nice things? (Directly substitute literals...)
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

CHR: known-boa-spec @ { Instance ?c A{ ?v } } // AS: ?p <={ Boa ?c ?i ?o } -- |
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
M: Slot live-vars val>> 1array ;
M: Slot defines-vars [ n>> ] [ val>> ] bi 2array ;
M: Instance live-vars val>> 1array ;
M: Instance defines-vars type>> defines-vars ;
M: Tag live-vars val>> 1array ;
M: Tag defines-vars var>> 1array ;
M: Iterated defines-vars [ next>> vars ] [ end>> vars ] bi union ;
! M: expr-pred defines-vars
! M: MacroCall live-vars out>> vars ;

! *** Phi Mode
! CHR: discard-non-union-pred @ { PhiMode } <={ MakeEffect } // <={ body-pred } -- | ;
! CHR: discard-leftover-binds @ { PhiMode } <={ MakeEffect } // <={ Bind } -- | ;
CHR: phi-discard-leftover-params @ { PhiMode } <={ MakeEffect } // <={ Param } -- | ;
CHR: phi-discard-phi-defs @ { PhiMode } <={ MakeEffect } // <={ Phi } -- | ;

! CHR: collect-union-preds @ { PhiMode } // { MakeEffect ?a ?b f ?l ?tau } { IsUnion ?p } --
! [ ?l ?p suffix :>> ?k ] |
! { MakeEffect ?a ?b f ?k ?tau } ;

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
! CHR: collect-body-pred @ // AS: ?e P{ MakeEffect ?a ?b ?x ?l ?tau } AS: ?p <={ body-pred } -- [ ?p live-vars ?e effect-vars subset? ]
CHR: collect-body-pred @ // AS: ?e P{ MakeEffect ?a ?b ?x ?l ?tau } AS: ?p <={ body-pred } -- [ ?p live-vars ?e effect-vars intersects? ]
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
! CHR: catch-unit-effect-call @ // { MakeEffect ?a ?b f f ?tau } { Literal ?q } { Instance ?q ?rho } { CallEffect ?q ?a ?b } --
! [ ?rho term-var? not ]
! [ ?a term-var? ] [ ?b term-var? ] |
! [ ?tau ?rho ==! ] ;

CHR: conflicting-makes @ { MakeEffect __ __ __ __ __ } { MakeEffect __ __ __ __ __ } // -- | [ "recursive-make" throw f ] ;

! *** Sanity check
! CHR: must-cleanup @ { MakeEffect __ __ __ __ __ } AS: ?p <={ body-pred } // -- | [ ?p "leftovers" 2array throw f ] ;
CHR: cleanup-incomplete @ { MakeEffect __ __ __ __ __ } // AS: ?p <={ body-pred } -- | ;

! This is triggered if phi mode is aborted
CHR: finish-disjoint-effect @ { PhiMode } { MakeEffect __ __ __ __ ?tau } // { Params __ } { Invalid } -- |
[ ?tau null ==! ] ;

! This is triggered if composition modes determines the effect will terminate
CHR: finish-invalid-effect @ { MakeEffect __ __ __ __ ?tau } // { Params __ } { Invalid } -- |
[ ?tau P{ Effect ?a ?b f { P{ Invalid } } } ==! ] ;

CHR: finish-valid-effect @ AS: ?e P{ MakeEffect ?a ?b __ ?l ?tau } // { Params ?x } -- [ ?tau term-var? ]
[ ?x ?e effect-vars intersect :>> ?y ]
|
[ ?tau P{ Effect ?a ?b ?y ?l } ==! ] ;

CHR: finish-phi-reasoning @ // { MakeEffect __ __ __ __ ?tau } { PhiMode } -- [ ?tau term-var? not ] | { PhiDone } ;
CHR: finish-compositional-reasoning @ // { MakeEffect __ __ __ __ ?tau } -- [ ?tau term-var? not ] | ;

;

: qt ( quot -- res )
    InferType boa 1array chr-comp swap [ run-chr-query store>> ] with-var-names ;
