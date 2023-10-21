USING: accessors arrays assocs chr.factor chr.factor.util chr.parser chr.state
classes classes.tuple classes.tuple.private combinators
combinators.short-circuit effects generic generic.math generic.single kernel
kernel.private layouts lists macros macros.expander math math.private quotations
sequences sets slots.private terms types.util words ;

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
        { 4drop [ drop drop drop drop ] }
        { 2dup [ over over ] }
        { 3dup [ pick pick pick ] }
        { 2dip [ swap [ dip ] dip ] }
        { 3dip [ swap [ 2dip ] dip ] }
        { dupd [ [ dup ] dip ] }
        { -rot [ swap [ swap ] dip ] }
        { if [ ? call ] }
        { pick [ [ over ] dip swap ] }
        { > [ swap < ] }
        ! This is tricky.  The first version does not work if we only consider input/output deciders during phi checking,
        ! because not enough info is kept during composition.
        ! In any case, the alias for typing does not have the same execution semantics as the other one...
        { <= [ 2dup < [ 2drop t ] [ = ] if ] }
        ! { <= [ [ < ] [ = ] 2bi or ] }
        { >= [ swap <= ] }
        ! { - [ -1 * + ] }
        ! TODO: revisit
        { number= [ { number number } declare = ] }
        ! NOTE: Interesting: emulating this gives a sequential relation we don't want, also the implied eq for fixnums is too
        ! special? Not really, but inside =, it does not work as expected as of yet
        { both-fixnums? [ fixnum? [ fixnum? ] [ drop f ] if ] }
        ! ! NOTE: We don't use the both-fixnums short-cut here for reasoning
        ! Nope, changes semantics!
        ! { = [ 2dup eq? [ 2drop t ] [ 2dup both-fixnums? [ 2drop f ] [ equal? ] if ] if ] }
        ! This is according to the word props, but there are methods defined on complex!
        ! { /i [ { real real } declare / >integer ] }
    } at ;

! ! Are skipped from certain ops?
! : special-generic? ( word -- ? )
!     { + < instance? nth length nth-unsafe call throw } in? ;

CHRAT: chr-word-types { }

CHR: dont-wrap-classes-invalid @ // { WrapClasses __ __ null ?tau } -- |
[ ?tau null ==! ] ;

CHR: destruct-wrap-classes-xor @ // { WrapClasses ?i ?o P{ Xor ?c ?d } ?tau } -- |
{ WrapClasses ?i ?o ?c ?rho }
{ WrapClasses ?i ?o ?d ?sig }
{ MakeXor ?rho ?sig ?tau } ;

PREDICATE: single-method < method "method-generic" word-prop single-generic? ;

GENERIC: word-input-classes ( word -- seq )
M: single-method word-input-classes
    [ "method-class" word-prop ]
    [ "method-generic" word-prop dispatch# ] bi
    dispatch-decl ;

M: word word-input-classes
    {
    [ "input-classes" word-prop ]
    [ "derived-from" word-prop dup [ rest ] when ]
    [ stack-effect effect-in-types ]
    } 1|| ;

! NOTE: not using ComposeType because this may not rebuild the effect!
CHR: add-default-classes-to-effect @ // { WrapDefaultClasses ?w ?e ?tau } --
|
[| |
 ?w word-input-classes :> in-types
 ?w { [ "default-output-classes" word-prop ]
      [ stack-effect effect-out-types ]
    } 1|| :> out-types
 { WrapClasses in-types out-types ?e ?tau }
] ;

! NOTE: not using ComposeType because this may not rebuild the effect!
CHR: add-classes-to-effect @ // { WrapClasses ?i ?o P{ Effect ?a ?b ?l ?p } ?tau } -- |
[| |
 ?i length "in" <array> elt-vars dup :> ain
 ?o length "out" <array> elt-vars dup :> aout
 ! [ >list __ list* ] bi@ :> ( lin lout )
 [ >list "rest" utermvar list* ] bi@ :> ( lin lout )
 ain <reversed> ?i
 [ DeclaredInstance boa ] 2map
 aout <reversed> ?o
 [ DeclaredInstance boa ] 2map append ?p append :> preds
 { ?a ?b } { lin lout } ==!
 ?tau P{ Effect ?a ?b ?l preds } ==!
 2array
] ;


! TODO: maybe insert input/output declarations here, too!
CHR: alias-type-defined @ { TypeOfWord ?w M{ ?tau } } // -- [ ?w word-alias :>> ?q ] |
{ ?TypeOf ?q ?tau } ;

! NOTE: changing these to caching because this does not use index lookup
CHR: type-of-prim-call @ { TypeOfWord (call) M{ ?tau } } // -- |
[ ?tau P{ Effect L{ ?q . ?a } ?b f {
              P{ Instance ?q quotation }
              P{ CallEffect ?q ?a ?b } } } ==! ] ;

CHR: type-of-call @ { TypeOfWord call M{ ?tau }  } // -- |
[ ?tau P{ Effect L{ ?q . ?a } ?b f {
              P{ Instance ?q callable }
              P{ CallEffect ?q ?a ?b } } } ==! ] ;

CHR: type-of-dip @ { TypeOfWord dip M{ ?tau } } // -- |
[ ?tau P{ Effect L{ ?q ?x . ?a } L{ ?x . ?b } f {
              P{ Instance ?q callable }
              P{ Instance ?x object }
              P{ CallEffect ?q ?a ?b } } }
  ==! ] ;

CHR: type-of-dup @ { TypeOfWord dup M{ ?tau } } // -- |
[ ?tau P{ Effect L{ ?x . ?rho } L{ ?x ?x . ?rho } f { P{ Instance ?x object } } } ==! ] ;

CHR: type-of-drop @ { TypeOfWord drop M{ ?tau } } // -- |
[ ?tau P{ Effect L{ ?x . ?a } ?a f { P{ Instance ?x object } } } ==! ] ;

CHR: type-of-swap @  { TypeOfWord swap M{ ?tau }  } // -- |
[ ?tau P{ Effect L{ ?x ?y . ?a } L{ ?y ?x . ?a } f { P{ Instance ?x object } P{ Instance ?y object } } } ==! ] ;

! *** Parameter-inducing words

CHR: type-of-mux @ { TypeOfWord ? M{ ?tau }  } // -- |
[
    ?tau
    P{ Xor
       P{ Effect L{ ?q ?p ?c . ?a } L{ ?p . ?a } { ?c } { P{ Instance ?q object } P{ Instance ?p object } P{ Instance ?c not{ POSTPONE: f } } P{ Neq ?c f } } }
       P{ Effect L{ ?q ?p ?c . ?a } L{ ?q . ?a } { ?c } { P{ Instance ?q object } P{ Instance ?p object } P{ Instance ?c POSTPONE: f } P{ Eq ?c f } } }
     }
    ==!
] ;

CHR: type-of-predicate @ { TypeOfWord ?w M{ ?tau } } // --
[ ?w word? ] [ ?w "predicating" word-prop :>> ?c ]
[ ?c 1quotation [ instance? ] compose :>> ?p ]
| { ?TypeOf ?p ?tau } ;

! NOTE: There is kind of a chicken-and-egg situation with instance checks and declarations.  There seems to
! be some kind of mutually recursive dependency between normative declaration and predicate
! checking.  Solution so far was to map everything to [ foo instance? ] semantics, which are then
! expanded when the class of DeclaredInstance becomes known.  This is expensive though, as it is a deferred inference.
CHR: type-of-instance? @ { TypeOfWord instance? M{ ?tau } } // -- |
[ ?tau P{ Xor
          P{ Effect L{ ?sig ?o . ?a } L{ ?c . ?a } f {
                 P{ DeclaredInstance ?o ?sig }
                 P{ Instance ?c t }
                 P{ Eq ?c t }
                 P{ Instance ?sig classoid }
             } }
          P{ Effect L{ ?sig ?o . ?a } L{ ?c . ?a } f {
                 P{ DeclaredNotInstance ?o ?sig }
                 P{ Instance ?c POSTPONE: f }
                 P{ Eq ?c f }
                 P{ Instance ?sig classoid }
             } }
          } ==! ] ;

! : <array> ( n elt -- array )
! NOTE: introducing a virtual "default" location
! Too complicated.  Treat the Element thing as default location itself
CHR: type-of-<array> @ { TypeOfWord <array> M{ ?tau } } // -- |
[ ?tau
  P{ Effect L{ ?v ?n . ?r } L{ ?a . ?r } f {
         P{ Instance ?n fixnum } ! would be array capacity, but that is quite verbose
         P{ Instance ?a array }
         P{ Instance ?v object }
         P{ Slot ?a 1 ?n }
         P{ Length ?a ?n }
         P{ Element ?a ?v }
         ! P{ Element ?a ?x }
         ! P{ PushLoc ?x f L{ ?v } ?r }
         P{ LocalAllocation ?r ?a }
     } }
  ==! ] ;

! ! : array-nth ( n array -- elt )
! ! NOTE: existentials
! CHR: type-of-array-nth @ { TypeOfWord array-nth ?tau } // -- |
! [ ?tau
!   P{ Effect L{ ?l ?n . ?a } L{ ?v . ?a } { ?x } {
!          P{ Instance ?n fixnum }
!          ! P{ Instance ?n array-capacity }
!          P{ Instance ?l array }
!          ! P{ Instance ?x array-capacity }
!          P{ DeclaredInstance ?x array-capacity }
!          P{ Instance ?v object }
!          P{ Length ?l ?x }
!          P{ Le ?n ?x }
!          ! P{ Element ?l ?v }
!          P{ Nth ?v ?l ?n }
!      } }
!   ==! ] ;

! TODO: convert slot accesses to ro-slots! (optimization)

! : slot ( obj m -- value )
CHR: type-of-slot @ { TypeOfWord slot M{ ?tau } } // -- |
[ ?tau
  P{ Effect L{ ?m ?o . ?a } L{ ?v . ?a } { ?b } {
  ! P{ Effect L{ ?m ?o . ?a } L{ ?v . ?a } f {
         P{ Instance ?o not{ integer } }
         P{ Instance ?m fixnum }
         P{ Instance ?v object }
         P{ Le 0 ?m }
         ! P{ SlotLoc ?x ?o ?m }
         P{ Slot ?o ?m ?x }
         P{ LocPop ?x ?a L{ ?v } ?b f ?a }
         P{ PushLoc ?x ?b L{ ?v } ?a f }
     } }
  ==! ] ;

! TODO annotate set-local-value and local-value with LocalAllocation predicates!
! (although that should probably only be an optimization)

! : set-slot ( value obj n -- )
CHR: type-of-set-slot @ { TypeOfWord set-slot M{ ?tau } } // -- |
[ ?tau
  P{ Effect L{ ?n ?o ?v . ?a } ?c { ?b ?z } {
  ! P{ Effect L{ ?n ?o ?v . ?a } ?b f {
         P{ Instance ?n fixnum }
         P{ Instance ?o not{ integer } }
         P{ Instance ?v object }
         P{ Le 0 ?n }
         ! P{ SlotLoc ?x ?o ?n }
         P{ Slot ?o ?n ?x }
         P{ LocPop ?x ?a L{ ?z } ?b f ?a }
         P{ PushLoc ?x ?b L{ ?v } ?c f }
     } }
  ==!
] ;

CHR: type-of-throw @ { TypeOfWord throw M{ ?tau } } // -- |
! [ ?tau P{ Effect ?a +bottom+ f } ==! ] ;
! [ ?tau null ==! ] ;
[ ?tau P{ Effect L{ ?e . ?a } ?b f {
              ! P{ Throws ?e }
              P{ Invalid }
          } }
  ==! ] ;

! TODO: possibly do this as macro expansion?  Would be the first
! case of a generic inline method kind of thing...
CHR: type-of-boa @ { TypeOfWord boa M{ ?tau } } // -- |
[ ?tau
  P{ Effect L{ ?c . ?a } L{ ?v . ?b } f { P{ Instance ?c tuple-class } P{ Boa ?c ?a L{ ?v . ?b } }
                                          P{ Instance ?v tuple } P{ LocalAllocation ?b ?v } } }
  ==!
] ;

CHR: type-of-tuple-boa @ { TypeOfWord <tuple-boa> M{ ?tau } } // -- |
[ ?tau
  P{ Effect L{ ?c . ?a } L{ ?v . ?b } f { P{ Instance ?c array } P{ TupleBoa ?c ?a L{ ?v . ?b } }
                                          P{ Instance ?v tuple } P{ LocalAllocation ?b ?v } } }
  ==!
] ;


! *** Preserve wrapper objects
CHR: type-of-wrapper @ // { ?TypeOf ?q ?tau } --
[ ?q callable? ]
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

CHR: type-of-pushed-quot @ { ?TypeOf Bind( ?p [ ?q ] ) ?tau } // -- [ ?q callable? ] |
{ ?TypeOf ?q ?rho }
{ MakeUnit ?rho ?sig }
{ ComposeType ?sig P{ Effect L{ ?x . ?a } L{ ?x . ?a } f { P{ Eq ?x ?q } } } ?c }
{ TypeOf ?p ?c } ;

CHR: type-of-unit-val @ { ?TypeOf Bind( ?p [ ?v ] ) ?tau } // -- [ ?v callable-word? not ] [ ?v callable? not ]
[ ?v dup eq-wrap? :>> ?l [ obj>> ] when :>> ?o drop t ] [ ?o precise-class-of :>> ?c ]
|
[ ?p P{ Effect ?a L{ ?x . ?a } f {
            P{ Instance ?x ?c }
            P{ Eq ?x ?o }
        } }
  ?l [ [ P{ LocalAllocation ?a ?x } suffix ] change-preds ] when
  TypeOf boa ] ;

! ! { ?TypeOf ?v ?rho }
! { MakeUnit ?rho ?sig }
! { TypeOf [ ?v ] ?sig } ;

! NOTE: Big Change! Only make these CallXors!
! Interestingly enough, it does not seem to have much impact, at least according
! to some very quick and rough tests
! CHR: make-xor-unit-type @ // { MakeUnit P{ Xor ?x ?y } ?tau } -- |
! { MakeXor ?rho ?sig ?tau }
! { MakeUnit ?x ?rho }
! { MakeUnit ?y ?sig } ;

! CHR: make-unit-local-alloc @ // { MakeUnit A{ ?o } ?tau } -- [ ?o local-alloc-val? ] |
! [ ?tau P{ Effect ?a L{ ?x . ?a } f { P{ Instance ?x ?o } P{ LocalAllocation ?a ?x } } } ==! ] ;

! CHR: make-unit-simple-type @ // { MakeUnit ?rho ?tau } -- [ { ?rho } first valid-type? ] |
CHR: make-unit-simple-type @ // { MakeUnit ?rho ?tau } -- [ ?rho term-var? not ] |
[ ?tau P{ Effect ?a L{ ?x . ?a } f { P{ Instance ?x ?rho } } } ==! ] ;

! *** Data Values

! CHR: type-of-val @ // { ?TypeOf A{ ?v } ?tau } -- [ ?v callable? not ] [ ?v callable-word? not ]
! |
! [ ?tau W{ W{ ?v } } ==! ] ;

! *** Some Primitives
! TODO: We don't express that there is at least one non-fixnum here.  Could be
! considered not a correct disjunct type?
! CHR: type-of-both-fixnums? @ { TypeOfWord both-fixnums? ?tau } // -- |
! { WrapDefaultClasses both-fixnums?
!   P{ Xor
!      P{ Effect L{ ?x ?y . ?a } L{ ?c . ?a } f {
!             { Instance ?x fixnum }
!             { Instance ?y fixnum }
!             { Instance ?c W{ t } } } }

!      P{ Effect L{ ?x ?y . ?a } L{ ?c . ?a } f {
!             { Instance ?x object }
!             { Instance ?y object }
!             ! { NotSame ?x ?y }
!             { Instance ?c W{ f } } }
!    } } ?tau } ;

CHR: type-of-eq @ { TypeOfWord eq? M{ ?tau } } // -- |
[ ?tau P{ Xor
          ! P{ Effect L{ ?x ?x . ?a } L{ ?c . ?a } f { P{ Instance ?x object } P{ Instance ?c t } P{ Eq ?c t } } }
          P{ Effect L{ ?x ?y . ?a } L{ ?c . ?a } f { P{ Instance ?x object } P{ Instance ?y object } P{ Instance ?c t } P{ Eq ?c t } P{ Eq ?x ?y } } }
          P{ Effect L{ ?x ?y . ?a } L{ ?c . ?a } f { P{ Instance ?x object } P{ Instance ?y object } P{ Instance ?c POSTPONE: f } P{ Eq ?c f } P{ NotSame ?x ?y } } }
   } ==! ] ;

! NOTE: Declarations are nominative first of all, although the existing type inference does
! treat declarations as type intersections.
CHR: type-of-declare @ { TypeOfWord declare M{ ?tau } } // -- |
[ ?tau
  P{ Effect L{ ?l . ?a } ?a f {
         P{ Instance ?l array }
         P{ DeclareStack ?l ?a }
     } }
  ==! ] ;

! : tag ( object -- n )
CHR: type-of-tag @ { TypeOfWord tag M{ ?tau } } // -- |
[ ?tau
  P{ Effect L{ ?o . ?a } L{ ?n . ?a } f {
         P{ Instance ?n fixnum }
         P{ Instance ?o object }
         P{ Tag ?o ?n }
     } } ==! ]  ;

! CONSTANT: primitive-coercers {
!     ! bignum fixnum is special because of precision loss.
!     ! Assuming Overflow to be an error
!     ! bignum>fixnum
!     fixnum>bignum
!     fixnum>float
! }

! Assume error on overflow conversion.  Not writing as XOR since it would be
! reasoned out anyways.
! bignum>fixnum ( x -- y )
CHR: type-of-bignum>fixnum @ { TypeOfWord bignum>fixnum M{ ?tau } } // --
[ most-positive-fixnum :>> ?u ]
[ most-negative-fixnum :>> ?l ] |
[ ?tau P{ Effect L{ ?x . ?a } L{ ?y . ?a } f {
              P{ Instance ?x bignum }
              ! P{ Instance ?x integer }
              P{ Instance ?y fixnum }
              P{ Le ?x ?u }
              P{ Le ?l ?x }
              P{ Eq ?x ?y }
          } } ==! ] ;


! ! TODO: use wrapclass-thing
! CHR: type-of-other-primitive-coercion @ { TypeOfWord ?w ?tau } // --
! [ ?w primitive-coercers in? ]
! [ ?w "input-classes" word-prop first :>> ?rho ]
! [ ?w "default-output-classes" word-prop first :>> ?sig ]
! |
! [ ?tau
!   P{ Effect L{ ?x . ?a } L{ ?y . ?a } f {
!          P{ Instance ?x ?rho }
!          P{ Instance ?y ?sig }
!          P{ Eq ?y ?x }
!      } }
!   ==! ] ;

! general primitives
! NOTE: reinferring to catch the conversions as early as possible // --
! *** Derived Words

! TODO: do for all derived primitives
! NOTE: This doesn't work for e.g. shift, because of the coercer.
CHR: type-of-derived-word @ { TypeOfWord ?w M{ ?tau } } // --
[ ?w "derived-from" word-prop :>> ?l ]
[ ?l first 1quotation :>> ?q ] |
{ ?TypeOf ?q ?sig }
{ WrapDefaultClasses ?w ?sig ?tau } ;
! { WrapDefaultClasses ?w ?sig ?rho }
! { ReinferEffect ?rho ?z }
! { CheckXor ?w ?z ?tau } ;

! *** Locals
! Note: We consider local handling bi-variable effects since the predicates
! are coupled to states represented by the row effects.  The intention is that
! the corresponding row vars are equated once the virtual retain stack usage is
! balanced. This is handled by PrimCall expansion though

! *** Primitive Catch-all
CHR: type-of-other-primitives @ { TypeOfWord ?w M{ ?tau } } // --
[ ?w primitive? ] [ ?w word-alias not ]
[ ?w macro-quot not ]
[ ?w stack-effect :>> ?e effect>stacks :>> ?b drop :>> ?a ] |
{ WrapDefaultClasses ?w P{ Effect ?a ?b f { P{ PrimCall ?w ?a ?b } } } ?rho }
{ ReinferEffect ?rho ?tau } ;

! shift ( x n -- y )
! CHR: type-of-fixnum-shift-fast @ { TypeOfWord fixnum-shift-fast ?tau } // -- |
! [ ?tau P{ Effect L{ ?n ?x . ?a } L{ ?y . ?a } f {
!               P{ Instance ?n fixnum }
!               P{ Instance ?x fixnum }
!               P{ Instance ?y fixnum }
!               P{ Shift ?y ?x ?n }
!           } } ==! ] ;

! *** Math
! NOTE: for now, not making generic dispatches on math words.  For type reasoning, we don't look into this. by default

! CHR: type-of-+ @ { TypeOfWord A{ + } ?tau } // -- |
! { MakeGenericDispatch +
!   P{ Effect L{ ?x ?y . ?a } L{ ?z . ?a } f {
!          P{ Instance ?x number }
!          P{ Instance ?y number }
!          P{ Instance ?z number }
!          P{ Sum ?z ?x ?y } } } ?tau } ;

! CHR: type-of-* @ { TypeOfWord A{ * } ?tau } // -- |
! { MakeGenericDispatch +
!   P{ Effect L{ ?x ?y . ?a } L{ ?z . ?a } f {
!          P{ Instance ?z number }
!          P{ Instance ?x number }
!          P{ Instance ?z number }
!          P{ Prod ?z ?x ?y } } } ?tau } ;

! CHR: type-of-/ @ { TypeOfWord A{ / } ?tau } // -- |
! { MakeGenericDispatch /
!   P{ Effect L{ ?y ?x . ?a } L{ ?z . ?a } f {
!          P{ Instance ?x number }
!          P{ Instance ?y number }
!          P{ Instance ?z number }
!          ! P{ Prod 1 ?m ?y }
!          P{ Instance ?m number }
!          ! P{ Prod ?z ?x ?m }
!          P{ Prod ?x ?z ?y } } } ?tau } ;

! induces parameter
! ( x y -- ? )
CHR: type-of-< @ { TypeOfWord < M{ ?tau } } // -- |
! { MakeGenericDispatch <
!   P{ Effect L{ ?x ?y . ?a } L{ ?c . ?a } f {
!          { Instance ?x number }
!          { Instance ?y number }
!          { Instance ?c boolean }
!          { <==> ?c P{ Lt ?x ?y } }
!      } } ?tau } ;
[| |
    ! ?sig
    P{ Xor
       P{ Effect L{ ?y ?x . ?a } L{ ?z . ?a } f {
              P{ Instance ?z t }
              P{ Eq ?z t }
              P{ Lt ?x ?y }
              ! P{ Neq ?y ?x }
          } }
        P{ Effect L{ ?y ?x . ?a } L{ ?z . ?a } f {
               P{ Instance ?z POSTPONE: f }
               P{ Eq ?z f }
               P{ Le ?y ?x }
           } }
     }
    :> sig
{ ComposeType P{ Effect ?a ?a f { P{ Ensure { number number } ?a } } } sig ?tau }
] ;

! CHR: type-of-equal? @ { TypeOfWord equal? ?tau } // -- |
CHR: type-of-equal? @ { TypeOfWord equal? M{ ?tau } } // -- |
{ MakeGenericDispatch equal?
  P{ Effect L{ ?x ?y . ?a } L{ ?c . ?a } f {
         { Instance ?c t } { Eq ?c t } { Eql ?x ?y } } } ?rho }
{ MakeGenericDispatch equal?
  P{ Effect L{ ?x ?y . ?a } L{ ?c . ?a } f {
         { Instance ?c POSTPONE: f } { Eq ?c f } { Neq ?x ?y } } } ?sig }
{ MakeXor ?rho ?sig ?tau } ;
! [ ?tau
!   P{ Xor ?rho ?sig } ==! ] ;

! TODO: generic expansion once fixnums are excluded, or classes are disjunct if needed
CHR: type-of-= @ { TypeOfWord = M{ ?tau } } // -- |
! { MakeGenericDispatch =
! [ ?tau
!     P{ Effect L{ ?x ?y . ?a } L{ ?c . ?a  } f {
!            { Instance ?x object }
!            { Instance ?y object }
!            { Instance ?c boolean }
!            { <==> ?c P{ Eq ?x ?y } }
!        } }
!      ==! ] ;
!     ! ?tau } ;
[
    ?tau
    P{ Xor
       P{ Effect L{ ?y ?x . ?a } L{ ?z . ?a } f {
              P{ Instance ?z t }
              P{ Eq ?z t }
              P{ Eql ?x ?y }
          } }
       P{ Effect L{ ?y ?x . ?a } L{ ?z . ?a } f {
              P{ Instance ?z POSTPONE: f }
              P{ Eq ?z f }
              P{ Neq ?x ?y }
          } }
     }
    ==!
] ;

! TODO: number declaring outputs on Sum, Prod conversion
! TODO: re-insert math dispatch once classes are known.
! XXX: Making the assumption here that ALL implementations of the underlying
! generics here DO NOT contain stateful effects.
CHR: type-of-math-word @ { TypeOfWord ?w M{ ?tau } } // --
[ ?w math-generic? ]
|
[| | ?w stack-effect effect>stacks :> ( lin lout )
 ?w stack-effect [ in>> length ] [ out>> length ] bi :> ( ni no )
 lin lout [ list*>array but-last <reversed> ] bi@
 [ ni head ] [ no head ] bi* :> ( ain aout )
 lin L{ ?y ?x . __ } ==!
 lin lout [ lastcdr ] bi@ ==!
 ! { ReinferEffect P{ Effect L{ ?y ?x . ?a } ?b f {
 { ReinferEffect P{ Effect lin lout f {
                        P{ Instance ?y number }
                        P{ Instance ?x number }
                        P{ MathCall ?w ain aout }
                    } } ?tau }
 3array ] ;

! *** Sequence-related
CHR: type-of-length @ { TypeOfWord A{ length } M{ ?tau } } // --
|
{ MakeGenericDispatch length
  P{ Effect L{ ?s . ?a } L{ ?n . ?a } f {
         P{ Instance ?s sequence }
         P{ Instance ?n integer }
         P{ Le 0 ?n }
         P{ Length ?s ?n } } }
  ?tau } ;

CHR: type-of-nth @ { TypeOfWord nth M{ ?tau } } // -- |
{ MakeGenericDispatch nth
  P{ Effect L{ ?s ?n . ?a } L{ ?v . ?a } { ?x } {
         P{ Instance ?s sequence }
         P{ Instance ?n integer }
         P{ Le 0 ?n }
         ! Existential
         P{ Length ?s ?x }
         P{ Instance ?x integer }
         P{ Lt ?n ?x  }
     } } ?tau } ;
! { nth-unsafe P{ Effect L{ ?s ?n . ?a } L{ ?v . ?a } f {
!                     P{ Instance ?n integer }
!                     P{ Le 0 ?n }
!                     P{ Instance ?s sequence }
!                     P{ Element ?s ?v }
!                 } } }


! TODO: output types
! *** Typed words
CHR: type-of-typed-word @ { TypeOfWord A{ ?w } M{ ?tau } } // --
[ ?w "typed-def" word-prop :>> ?q ]
[ ?w "declared-effect" word-prop effect-in-types <reversed> >list :>> ?a ]
|
{ ?TypeOf ?q ?rho }
! FIXME: check declaration order!
{ ComposeType P{ Effect ?x ?x f { P{ Declare ?a ?x } } } ?rho ?tau } ;

! *** Delayed Expansion words

CONSTANT: force-compile
{ if }

: handle-word-as-macro? ( word -- ? )
    dup force-compile in? [ drop f ]
    [ { [ "transform-n" word-prop ]
        [ macro? ]
      } 1|| ] if ;

: macro-input>expander-stacks ( n -- lin lout )
    ! "i" swap "a" <array> "o" { "quot" } <variable-effect>
    "a" <array> { "quot" } <effect>
    effect>stacks ;

: macro-input>stack ( n -- lin )
    macro-input>expander-stacks drop ;

! Macro stacks: L{ argn arg2 arg1 . in } out
! Sequence: L{ argn arg2 arg1 . in } --> L{ q . in } --> out where q is effect L{ in out }
! TODO: maybe handle declared classes of macros?
CHR: type-of-macro @ { TypeOfWord A{ ?w } M{ ?tau } } // --
[ ?w handle-word-as-macro? ]
[ ?w macro-effect :>> ?n ]
[ ?n macro-input>expander-stacks :>> ?b drop :>> ?a ]
[ ?a lastcdr :>> ?i drop t ]
[ ?b car :>> ?q drop t ]
[ ?w macro-quot :>> ?x ]
[ ?a list>array* ?n head reverse :>> ?p ]
|
[ ?tau P{ Effect ?a ?o { ?q } {
              P{ MacroCall ?x ?p ?q }
              ! P{ MacroExpand ?w f ?a ?q }
              P{ Instance ?q callable }
              P{ CallEffect ?q ?i ?o }
          } }
==! ]
;

! ** Regular Words

CHR: type-of-regular-word @ { TypeOfWord A{ ?w } M{ ?tau } } // --
[ ?w word-alias not ]
[ ?w method? not ]
[ ?w callable-word? ]
[ ?w "no-compile" word-prop not ]
[ ?w "predicating" word-prop not ]
! [ ?w "transform-quot" word-prop not ]
[ ?w generic? not ]
[ ?w def>> ?w 1quotation = not ]
[ ?w def>> quote-literals :>> ?q ]
! NOTE: trying to assess whether we ever hit this case at all!
[ ?w "input-classes" word-prop >array :>> ?c dup length 1 > [ { ?w "input-class-ensure-on-regular-word" } throw ] when ]
|
{ ?TypeOf ?q ?sig }
{ ComposeType P{ Effect ?a ?a f { P{ Ensure ?c ?a } } } ?sig ?tau } ;

! ** Generic Dispatch

! TODO: rebuild this as quotations again to make sure this uses the same inference path
! as other mutually recursive definitions.  The difference would be that here the recursion is actually hit during
! "macro" expansion in a dispatch instead of the initial type query tree building?

! NOTE: we cannot assume any effects to be non-bi-variable when they can contain effect sequencing predicates!!!
CHR: make-single-or-math-generic-dispatch @ // { MakeGenericDispatch ?w P{ Effect ?i ?o ?l ?p } ?tau } --
! [ ?w { [ single-generic? ] [ math-generic? ] } 0|| ]
[ ?w generic? ]
[ ?w stack-effect effect>stacks :>> ?b
  list*>array but-last :>> ?y drop
  :>> ?a list*>array but-last :>> ?x ]
[
    ?x
    { { [ ?w single-generic? ] [ ?w dispatch# swap nth 1array ] }
      { [ ?w math-generic? ] [ first2 2array ] }
    } cond :>> ?d ]
[ ?p P{ GenericDispatch ?w ?d ?y ?a ?b } suffix :>> ?q ]
|
[ { ?i ?o } { ?a ?b } ==! ]
{ WrapDefaultClasses ?w P{ Effect ?i ?o ?l ?q } ?tau } ;


! NOTE: don't evaluate into the default method if open-world assumption is made instead
CHR: type-of-generic @ { TypeOfWord ?w M{ ?tau } } // --
[ ?w generic? ]
! [ ?w dispatch# :>> ?i ]
[ ?w "transform-quot" word-prop not ]
! [ ?w dispatch-method-seq >list :>> ?l ]
! [ ?w stack-effect effect>stacks :>> ?b drop :>> ?a ]
! [ ?i ?a list*>array but-last <reversed> nth :>> ?d ]
|
{ MakeGenericDispatch ?w P{ Effect ?a ?b f f } ?tau } ;
! [ ?tau P{ Effect ?a ?b f { ?sig } } ==! ] ;
! [ ?tau P{ Effect ?a ?b f { P{ GenericDispatch ?w { ?d } ?a ?b } } } ==! ] ;
! { MakeSingleDispatch ?i ?l ?tau } ;

! ! NOTE: this really belongs to intra-effect!
! CHR: expand-single-generic-dispatch @ { CompMode } { Instance ?x A{ ?c } } // { GenericDispatch ?w { x } ?a ?b } -- |
! [ ?w single-generic? ]
! [ ?c bounded-class? ]
! [ ?w dispatch# :>> ?i ]
! [ ?w dispatch-method-seq [ ?c classes-intersect? ] filter-keys
!   >list :>> ?l ] |
! { MakeSingleDispatch ?i ?l ?rho }

! CHR: dispatch-done @ // { MakeSingleDispatch __ +nil+ ?tau } -- | [ ?tau null ==! ] ;

! CHR: dispatch-case @ // { MakeSingleDispatch ?i L{ { ?c ?m } . ?r } ?tau } --
! [ ?c ?i dispatch-decl <reversed> >list :>> ?l ]
! |
! { TypeOfWord ?m ?a }
! ! TODO: make this a declare quot instead of pred?
! ! Here we prefix the method word type with the excluded cases from the ordered dispatch
! { ComposeType P{ Effect ?b ?b f { P{ Declare ?l ?b } } } ?a ?rho }
! { MakeSingleDispatch ?i ?r ?sig }
! { MakeXor ?rho ?sig ?d }
! { CheckXor ?m ?d ?tau } ;

CHR: type-of-single-method @ { TypeOfWord ?w M{ ?tau } } // --
[ ?w single-method? ]
[ ?w def>> quote-literals :>> ?q ] |
{ ?TypeOf ?q ?rho }
{ WrapDefaultClasses ?w ?rho ?tau } ;


CHR: type-of-empty-quot @ // { ?TypeOf [ ] ?tau } -- | [ ?tau P{ Effect ?a ?a f f } ==! ] ;

! TODO: expand macros early
CHR: type-of-proper-quot @ { ?TypeOf ?q ?tau } // -- [ ?q callable? ] [ ?q length 1 > ]
[ \ do-primitive ?q in? not ]
[ ?q dup length 2 /i cut :>> ?y drop :>> ?x drop t ] |
{ ?TypeOf ?x ?rho }
{ ?TypeOf ?y ?sig }
{ ComposeType ?rho ?sig ?a }
{ CheckXor ?q ?a ?b }
{ TypeOf ?q ?b } ;

;
