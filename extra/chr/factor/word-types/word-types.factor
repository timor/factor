USING: accessors arrays assocs chr.factor chr.parser chr.state classes
classes.algebra classes.builtin classes.predicate classes.tuple
classes.tuple.private classes.union combinators.short-circuit effects generic
generic.single kernel kernel.private lists macros macros.expander math
math.private namespaces quotations sequences sequences.private sets
slots.private terms types.util words ;

IN: chr.factor.word-types

! * Answer word type requests

! Predefined words and destructuring

: word-alias ( word -- def/f )
    H{
        { rot [ [ swap ] dip swap ] }
        { over [ swap dup [ swap ] dip ] }
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
        { number= [ { number number } declare = ] }
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

CHRAT: chr-word-types { }


CHR: alias-type-defined @ { TypeOfWord ?w ?tau } // -- [ ?w word-alias :>> ?q ] |
{ ?TypeOf ?q ?tau } ;

CHR: type-of-prim-call @ // { ?TypeOf [ (call) ] ?tau } -- |
[ ?tau P{ Effect L{ ?q . ?a } ?b f {
              P{ Instance ?q quotation }
              P{ CallEffect ?q ?a ?b } } } ==! ] ;

CHR: type-of-call @ // { ?TypeOf [ call ] ?tau } -- |
[ ?tau P{ Effect L{ ?q . ?a } ?b f {
              P{ Instance ?q callable }
              P{ CallEffect ?q ?a ?b } } } ==! ] ;

CHR: type-of-dip @ { TypeOfWord dip ?tau } // -- |
[ ?tau P{ Effect L{ ?q ?x . ?a } L{ ?x . ?b } f {
              P{ Instance ?q callable }
              P{ Instance ?x object }
              P{ CallEffect ?q ?a ?b } } }
  ==! ] ;

CHR: type-of-dup @ { TypeOfWord dup ?tau } // -- |
[ ?tau P{ Effect L{ ?x . ?rho } L{ ?x ?x . ?rho } f { P{ Instance ?x object } } } ==! ] ;

CHR: type-of-drop @ // { ?TypeOf [ drop ] ?tau } -- |
[ ?tau P{ Effect L{ ?x . ?a } ?a f { P{ Instance ?x object } } } ==! ] ;

CHR: type-of-swap @ // { ?TypeOf [ swap ] ?tau } -- |
[ ?tau P{ Effect L{ ?x ?y . ?a } L{ ?y ?x . ?a } f { P{ Instance ?x object } P{ Instance ?y object } } } ==! ] ;

! *** Parameter-inducing words

CHR: type-of-mux @ // { ?TypeOf [ ? ] ?tau } -- |
[
    ?tau
    P{ Xor
       P{ Effect L{ ?q ?p ?c . ?a } L{ ?p . ?a } { ?c } { P{ Instance ?q object } P{ Instance ?p object } P{ Instance ?c not{ POSTPONE: f } } } }
       P{ Effect L{ ?q ?p ?c . ?a } L{ ?q . ?a } { ?c } { P{ Instance ?q object } P{ Instance ?p object } P{ Instance ?c POSTPONE: f } } }
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
            P{ Instance ?y t }
        } }
     ! P{ Effect L{ ?x . ?a } L{ ?y . ?a } { ?x ?y } {
     P{ Effect L{ ?x . ?a } L{ ?y . ?a } { ?y } {
            P{ Instance ?x ?d }
            P{ Instance ?y POSTPONE: f }
        } }
   }
  ==!
] ;

! NOTE: don't use internal optimized implementations here
GENERIC: make-pred-quot ( class -- quot )


! { real fixnum array }
! [ dup real? [ nip ] [ dup fixnum? [ nip ] [ array? ] if* ] if* ]
M: union-class make-pred-quot
    "members" word-prop <reversed> unclip "predicate" word-prop
    swap
    [ ! ( acc class )
     "predicate" word-prop swap
     '[ dup @ [ nip ] _ if* ]
    ] each ;

! NOTE: relies on implementation detail of the predicate quotation being a singular
! quotation!
M: predicate-class make-pred-quot "predicate" word-prop first def>> ;

CHR: type-of-predicate @ { TypeOfWord ?w ?tau } // -- [ ?w "predicating" word-prop :>> ?c ]
[ ?c class-not :>> ?d ]
[ ?c make-pred-quot :>> ?p ]
[ [ ?p keep over [ { ?c } declare drop ] [ { ?d } declare drop ] if ] :>> ?q ]
|
{ ?TypeOf ?q ?tau } ;

! NOTE: this is kind of a chicken-and-egg situation with instance checks.  There seems to
! be some kind of mutually recursive dependency between normative declaration and predicate
! checking.
! For now: try to rewrite it to merge with the type-of-predicate code path
CHR: type-of-instance? @ { TypeOfWord instance? ?tau } // -- |
[ ?tau P{ Xor
          P{ Effect L{ ?sig ?o . ?a } L{ ?c . ?a } { ?c } {
                 P{ Instance ?o ?sig }
                 P{ Instance ?c t }
                 P{ Instance ?sig classoid }
             } }
          P{ Effect L{ ?sig ?o . ?a } L{ ?c . ?a } { ?c } {
                 P{ NotInstance ?o ?sig }
                 P{ Instance ?c POSTPONE: f }
                 P{ Instance ?sig classoid }
             } }
          } ==! ] ;

! UNION: decomposable-class union-class predicate-class ;

! CHR: expand-instance-check @ // { Instance ?x A{ ?rho } } -- [ { ?rho } first wrapper? ] [ { ?rho } first wrapped>> decomposable-class?  ]
! [ { ?rho } first wrapped>> make-pred-quot :>> ?c ]
! [  ]
! |
! {  }

! : <array> ( n elt -- array )
CHR: type-of-<array> @ { TypeOfWord <array> ?tau } // -- |
[ ?tau
  P{ Effect L{ ?v ?n . ?r } L{ ?a . ?r } { ?v } {
         P{ Instance ?n fixnum }
         P{ Instance ?a array }
         P{ Instance ?v object }
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
         P{ Instance ?v object }
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
         P{ Instance ?v object }
         P{ Slot ?o ?m ?v }
     } }
  ==! ] ;

! : set-slot ( value obj n -- )
CHR: type-of-set-slot @ { TypeOfWord set-slot ?tau } // -- [ ?tau term-var? ] |
[ ?tau
  P{ Effect L{ ?n ?o ?v . ?a } ?a f {
         P{ Instance ?n fixnum }
         P{ Instance ?o not{ fixnum } }
         P{ Instance ?v object }
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


! *** Preserve wrapper objects
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

! *** Destructure unit type queries

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

! *** Data Values

CHR: type-of-val @ // { ?TypeOf A{ ?v } ?tau } -- [ ?v callable? not ] [ ?v callable-word? not ]
|
[ ?tau W{ W{ ?v } } ==! ] ;

! *** Some Primitives

! induces parameter
CHR: type-of-eq @ { TypeOfWord eq? ?tau } // -- |
[ ?tau P{ Xor
          ! introducing the value which is equal to as parameter?
          P{ Effect L{ ?x ?x . ?a } L{ ?c . ?a } { ?c } { P{ Instance ?x object } P{ Instance ?c t } } }
          P{ Effect L{ ?x ?y . ?a } L{ ?c . ?a } { ?c } { P{ Instance ?x object } P{ Instance ?c POSTPONE: f } P{ Neq ?x ?y } } }
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
         P{ Instance ?o object }
         P{ Tag ?o ?n }
     } } ==! ]  ;

CONSTANT: primitive-coercers {
    bignum>fixnum
    fixnum>bignum
    fixnum>float
}
! bignum>fixnum ( x -- y )
CHR: type-of-primitive-coercion @ { TypeOfWord ?w ?tau } // --
[ ?w primitive-coercers in? ]
[ ?w "input-classes" word-prop first :>> ?rho ]
[ ?w "default-output-classes" word-prop first :>> ?sig ]
|
[ ?tau
  P{ Effect L{ ?x . ?a } L{ ?y . ?a } f {
         P{ Instance ?x ?rho }
         P{ Instance ?y ?sig }
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

! induces parameter
! ( x y -- ? )
CHR: type-of-< @ { TypeOfWord A{ < } ?tau } // -- |
[
    ?sig
    P{ Xor
       P{ Effect L{ ?y ?x . ?a } L{ ?z . ?a } { ?z } {
              P{ Instance ?z t }
              P{ Lt ?x ?y }
              ! P{ Neq ?y ?x }
          } }
        P{ Effect L{ ?y ?x . ?a } L{ ?z . ?a } { ?z } {
               P{ Instance ?z POSTPONE: f }
               P{ Le ?y ?x }
           } }
     }
    ==!
]
{ ComposeType P{ Effect ?a ?a f { P{ Ensure { number number } ?a } } } ?sig ?tau } ;

! induces parameter
CHR: type-of-= @ { TypeOfWord A{ = } ?tau } // -- |
[
    ! ?sig
    ?tau
    P{ Xor
       P{ Effect L{ ?x ?y . ?a } L{ ?z . ?a } { ?z } {
              P{ Instance ?z t }
              P{ Eq ?x ?y }
          } }
       P{ Effect L{ ?x ?y . ?a } L{ ?z . ?a } { ?z } {
              P{ Instance ?z POSTPONE: f }
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

! *** Delayed Expansion words

CONSTANT: force-compile
{ if }

: handle-word-as-macro? ( word -- ? )
    dup force-compile in? [ drop f ]
    [ { [ "transform-n" word-prop ]
        [ macro? ]
      } 1|| ] if ;

: macro-input>stack ( n -- lin )
    "i" swap "a" <array> "o" { "quot" } <variable-effect>
    effect>stacks drop ;

! TODO: maybe handle declared classes of macros?
CHR: type-of-macro @ { TypeOfWord A{ ?w } ?tau } // --
[ ?tau term-var? ]
[ ?w handle-word-as-macro? ]
[ ?w macro-effect macro-input>stack :>> ?a drop t ]
[ ?a lastcdr :>> ?i drop t ]
|
[ ?tau P{ Effect ?a ?o { ?q } {
              P{ MacroExpand ?w f ?a ?q }
              P{ Instance ?q callable }
              P{ CallEffect ?q ?i ?o }
          } }
==! ]
;

! GENERIC: instance-check-quot ( classoid -- quot )
! M: builtin-class instance-check-quot
!     nip
! : instance-check-quot ( classoid -- quot )


CHR: type-of-instance? @ { TypeOfWord instance? ?tau } // --
[ 1 macro-input>stack :>> ?i drop t ]
|
[ ?tau P{ Xor
          P{ Effect L{ ?sig ?o . ?a } L{ ?c . ?a } { ?q } {
                 P{ Instance ?o ?sig }
                 P{ Instance ?c t }
                 P{ Instance ?sig classoid }
                 P{ Instance ?q callable }
                 P{ InstanceCheck ?sig ?q t }
                 P{ CallEffect ?q L{ ?sig ?o . ?a } L{ ?c . ?a } }
             } }
          P{ Effect L{ ?sig ?o . ?a } L{ ?c . ?a } { ?q } {
                 P{ NotInstance ?o ?sig }
                 P{ Instance ?c POSTPONE: f }
                 P{ Instance ?sig classoid }
                 P{ Instance ?q callable }
                 P{ InstanceCheck ?sig ?q f }
                 P{ CallEffect ?q L{ ?sig ?o . ?a } L{ ?c . ?a } }
             } }
        } ==! ] ;


! ** Regular Words

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

;
