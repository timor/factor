USING: accessors arrays assocs chr.factor chr.factor.composition
chr.factor.effects chr.factor.intra-effect.liveness chr.factor.phi
chr.factor.util chr.parser chr.state chr.test classes classes.tuple combinators
combinators.short-circuit grouping kernel kernel.private layouts lists literals
locals.backend math math.private namespaces quotations quotations.private sequences slots
slots.private stack-checker.values strings terms tools.test typed types.util
words ;

IN: chr.factor.composition.tests

! reset-chr-types
clear-chr-cache

{ } [ cache-types? on ] unit-test
{ t } [ cache-types? get ] unit-test

! ** Testing external helper behavior
! TODO: move to util tests

! NOTE: this highlights an important point: if the think of
! intersection{ number tuple } as a nominative class specification, it is open
! as to who the implementors are.  However, rebuilding the the class explicitly
! using `number tuple class-and` will actually build the smallest cover out of
! the known subclasses at call time (known world assumption)
{ union{ ratio complex } }
[ intersection{ number tuple } simplify-class ] unit-test

{ integer }
[ intersection{ number integer } simplify-class ] unit-test

! { not{ list } }
{ intersection{ not{ cons-state } not{ L{ } } } }
[ not{ list } simplify-class ] unit-test

! { not{ list } }
{ intersection{ not{ cons-state } not{ L{ } } } }
[ intersection{ not{ list } } simplify-class ] unit-test

! { not{ list } }
{ intersection{ not{ cons-state } not{ L{ } } } }
[ intersection{ not{ cons-state } not{ L{ } } not{ list } } simplify-class ] unit-test

! ** Test Helpers
: chr-simp ( constraints -- constraint )
    P{ CompMode } suffix
    chr-comp swap [ run-chr-query solved-store ] with-var-names
    values P{ CompMode } swap remove
    ! [ Dep? ] reject
    ;

: chr-simp1 ( constraints -- constraint )
    chr-simp first ;

: same-type? ( quot quot -- ? )
    [ get-type ] bi@ same-effect? ;

TYPED: array-first ( arr: array -- thing ) 2 slot ;

TERM-VARS: ?o ?a ?b ?b1 ?v ?w ?x ?y ?z ;
TERM-VARS: ?y2 ?ys2 ?o4 ?a43 ?y6 ?ys6 ;
TERM-VARS: ?y1 ?ys1 ?x1 ?v1 ?x2 ?x3 ?rho1 ?rho2 ?rho3 ?o1 ?a1 ;
TERM-VARS: ?i1 ?q1 ?q2 ?z1 ?i4 ?z6 ?i2 ?c1 ?a2 ?z2 ;
TERM-VARS: ?c ?d ;
TERM-VARS: ?q3 ?q5 ?p2 ?p3 ?c2 ?c3 ?a4 ?a6 ?b3 ?b4 ;
TERM-VARS: ?a15 ?o3 ?v3 ;
TERM-VARS: ?o5 ?b34 ?v7 ;
TERM-VARS: ?y14 ?ys14 ?o25 ?a85 ?x17 ?rho31 ;

P{ Effect L{ ?o3 . ?a6 } L{ ?v3 . ?a6 } { ?x1 }
    {
        P{ Instance ?o3 array }
        P{ Instance ?v3 object }
        P{ Slot ?o3 2 ?x1 }
        P{ LocPop ?x1 ?a6 L{ ?v3 } ?a6 f ?a6 }
        P{ PushLoc ?x1 ?a6 L{ ?v3 } ?a6 f } } }
[ \ array-first get-type ] chr-test

[ { 42 } array-first ] [ [ { 42 } array-first ] call ] test-same-type

[ 1 drop 42 ] [ { 42 } array-first ] test-same-type
[ 1 drop 42 ] [ { 42 43 } array-first ] test-same-type

! ** Throwing
P{ Effect ?a ?b f { P{ Invalid } } }
[ [ "haha" throw ] get-type ] chr-test

! ** Unphiable stacks test
{ t } [ { ?a ?b } { ?v ?w } unify phi-stacks-unique? ] unit-test
{ f } [ { ?a ?b } { ?v ?v } unify phi-stacks-unique? ] unit-test
{ t } [ { L{ ?a ?b . ?v } ?v }
        { L{ ?c ?d ?x ?y . ?o } L{ ?x ?y . ?o } } unify
        phi-stacks-unique? ] unit-test
{ f } [ { L{ ?a ?b . ?v } ?v }
        { L{ ?c ?d ?x ?y . ?o } L{ ?y ?x . ?o } } unify
        phi-stacks-unique? ] unit-test
{ f } [ { L{ ?a ?x } L{ ?b ?x } }
        { L{ ?c ?d } L{ ?d ?c } } unify
        phi-stacks-unique? ] unit-test

{ f } [ { L{ ?a ?x . ?o } L{ ?b ?x . ?o } }
        { L{ ?c ?d . ?z } L{ ?d ?c . ?z } } unify
        phi-stacks-unique? ] unit-test

! ** Normalization
P{ Neq ?a 42 }
[ { P{ Neq ?a 42 } } chr-simp1 ] chr-test

P{ Neq ?a 42 }
[ { P{ Neq 42 ?a } } chr-simp1 ] chr-test

P{ Eq ?a 42 }
[ { P{ Eq 42 ?a } } chr-simp1 ] chr-test

P{ Neq ?a ?b }
[ { P{ Neq ?a ?b } } chr-simp1 ] chr-test
P{ Neq ?b ?a }
[ { P{ Neq ?b ?a } } chr-simp1 ] chr-test

{ { P{ Instance ?a number } } }
[ { P{ Neq ?a "haha" } P{ Instance ?a number } } chr-simp ] unit-test

! ** Basic Invariants
{ P{ Eq ?c { 43 } } }
[ { P{ Eq ?y1 ?a1 } P{ Eq ?x1 ?a1 } P{ Eq ?a1 { 43 } } P{ Eq ?y1 ?x1 } } chr-simp ] chr-test


{ t } [ { 43 } dup Eq boa tuple-slots first2 eq? ] unit-test
{ t } [ { 43 } dup Eq boa f lift tuple-slots first2 eq? ] unit-test
! Changed to work on all terms now
{ t } [ { 43 } dup Eql boa f lift tuple-slots first2 eq? ] unit-test
{ t } [ { 43 } dup NotSame boa f lift tuple-slots first2 eq? ] unit-test
{ t } [ { 43 } dup Neq boa f lift tuple-slots first2 eq? ] unit-test
{ t } [ P{ Eq ?x { 42 } } dup f lift [ val2>> ] bi@ eq? ] unit-test

{ { P{ Invalid } } } [ { P{ Neq 5 5 } } chr-simp ] unit-test
{ { P{ Invalid } } } [ { P{ Neq f f } } chr-simp ] unit-test
{ { P{ Invalid } } } [ { P{ Neq ?c ?c } } chr-simp ] unit-test
{ { P{ Neq ?c ?d } } } [ { P{ Neq ?c ?d } } chr-simp ] unit-test
{ { P{ Neq ?c 5 } } } [ { P{ Neq ?c 5 } } chr-simp ] unit-test
{ { } } [ { P{ Neq f t } } chr-simp ] unit-test

{ t } [ [ 1 drop \ +nil+ ] [ 1 drop +nil+ ] same-type? ] unit-test
{ t } [ [ 1 drop \ t ] [ 1 drop t ] same-type? ] unit-test
{ f } [ [ 1 drop \ f ] [ 1 drop f ] same-type? ] unit-test

{ t }
[ [ if* ] get-type valid-effect-type? ] unit-test

P{ Effect L{ ?a ?b . ?z } L{ ?a ?b . ?z } f { P{ Instance ?a object }
                                                P{ Instance ?b object } } }
[ [ swap swap ] get-type ] chr-test

P{ Effect L{ ?a ?b . ?z } L{ ?b ?a . ?z } f { P{ Instance ?a object }
                                                P{ Instance ?b object } } }
[ [ swap swap swap ] get-type ] chr-test

P{ Effect L{ ?y ?x . ?a } L{ ?z . ?a } f { P{ Instance ?x number } P{ Instance ?y number } P{ Instance ?z number } P{ Sum ?z ?x ?y } } }
[ [ + ] get-type ] chr-test

{ t }
[ [ [ ? ] ] [ [ [ ? ] ] (call) ] same-type? ] unit-test

{ t }
[ [ [ if ] ] [ [ [ if ] ] (call) ] same-type? ] unit-test

! This one freaks out the isomorphism checker?
! Seems to be fixed...
{ t }
[ [ [ [ if ] ] ]  [ [ [ [ if ] ] ] (call) ] same-type? ] unit-test

[ 2 + ] [ 2 swap + ] test-same-type
[ + ] [ swap + ] test-same-type
[ + swap + + ] [ + + swap + ] test-same-type
[ swap + swap + swap + ] [ + + + ] test-same-type
! NOTE: the following is actually not the same type, because overflow behavior
! could be different based on the data types???
! [ + 2 + ] [ 2 + + ] test-same-type

P{ Effect
   L{ ?x1 ?o1 . ?b1 } L{ ?x1 ?o1 . ?b1 } f {
       P{ Instance ?x1 callable }
       P{ Instance ?o1 object } } }
[ curry uncurry ] test-chr-type

P{ Effect
   L{ ?x1 ?o1 . ?b1 } L{ ?x1 ?o1 . ?b1 } f {
       P{ Instance ?x1 callable }
       P{ Instance ?o1 callable } } }
[ compose uncompose ] test-chr-type

[ 42 ] [ 42 [ ] curry call ] test-same-type

[ swap swap swap ] [ [ swap ] curry curry call ] test-same-type
! NOTE: This is interesting: because we have [ ? ] as basis, we don't enforce
! that the non-taken branch quotation is actually a quotation!
P{
    Xor
    ! subsumed
    ! P{ Effect L{ ?q3 ?p2 ?c2 . ?a4 } ?b3 f { P{ Instance ?q3 object } P{ Instance ?c2 not{ POSTPONE: f } } P{ Neq ?c f } P{ Instance ?p2 callable } P{ CallEffect ?p2 ?a4 ?b3 } } }
    P{ Effect L{ ?q3 ?p2 ?c2 . ?a4 } ?b3 f { P{ Instance ?q3 object } P{ Instance ?c2 not{ POSTPONE: f } } P{ Instance ?p2 callable } P{ CallEffect ?p2 ?a4 ?b3 } } }
    P{ Effect L{ ?q5 ?p3 ?c3 . ?a6 } ?b4 f { P{ Instance ?p3 object } P{ Instance ?c3 POSTPONE: f } P{ Eq ?c3 f } P{ Instance ?q5 callable } P{ CallEffect ?q5 ?a6 ?b4 } } }
}
[ [ if ] get-type ] chr-test

P{ Effect ?a ?b f { P{ Invalid } } }
[ [ 42 2 slot ] get-type ] chr-test

P{ Effect ?a ?b f { P{ Invalid } } }
[ [ curry (call) ] get-type ] chr-test

{ t }
[ [ compose call ] [ [ call ] dip call ] same-type? ] unit-test

{ f }
[ [ [ 42 2 slot ] [ "string" ] if ] [ drop "string" ] same-type? ] unit-test

{ t }
[ [ [ 42 2 slot ] [ "string" ] if ] [ { W{ f } } declare drop "string" ] same-type? ] unit-test

{ t } [ [ fixnum? 4 5 ? ] get-type Xor? ] unit-test

P{ Effect L{ ?y . ?a } L{ ?x . ?a } f
   { P{ Eq ?x 4 } P{ Instance ?x fixnum } P{ Instance ?y object } } }
[ [ number? 4 4 ? ] get-type ] chr-test

{ t }
[ [ number? 4 5 ? ] get-type Xor? ] unit-test

[ drop f ] [ dup (clone) eq? ] test-same-type

! ** Sums and Parameters


P{
    Effect
    L{ ?y1 ?x1 . ?rho1 }
    L{ ?z1 . ?rho1 }
    f
    { P{ Instance ?y1 number } P{ Instance ?x1 number } P{ Instance ?z1 number } P{ Sum ?z1 ?x1 ?y1 } }
} [ + ] test-chr-type

{ 1 2 3 4 5 }
[ { [ + ] [ + + ] [ + + + ] [ + + + + ] [ + + + + + ] }
  [ get-type preds>> [ Sum? ] count ] each
] unit-test

{ 1 2 3 4 5 }
[ { [ * ] [ * * ] [ * * * ] [ * * * * ] [ * * * * * ] }
  [ get-type preds>> [ Prod? ] count ] each
] unit-test

{ 1 2 3 4 5 }
[ { [ * ] [ + * ] [ + * + ] [ * - * + ] [ - + - * + ] }
  [ get-type preds>> [ { [ Prod? ] [ Sum? ] } 1|| ] count ] each
] unit-test

! Neuralgic for missing Sum mode
{ 2 } [ [ - 2 + ] get-type preds>> [ Sum? ] count ] unit-test
{ 3 } [ [ + 2 + + ] get-type preds>> [ Sum? ] count ] unit-test
{ 4 } [ [ + + 2 + + ] get-type preds>> [ Sum? ] count ] unit-test

{ 1 } [ [ slot + ] get-type preds>> [ Sum? ] count ] unit-test
{ 1 } [ [ 2 slot + ] get-type preds>> [ Sum? ] count ] unit-test
{ 1 } [ [ 2 slot swap 2 slot + ] get-type preds>> [ Sum? ] count ] unit-test

! NOTE: this will not reduce to 5 sums unless ordering partial known sums correctly?
{ 6 } [ [ + + 2 + + 3 + + ] get-type preds>> [ Sum? ] count ] unit-test
{ 3 } [ [ + 2 + - ] get-type preds>> [ Sum? ] count ] unit-test
{ 3 } [ [ - 2 swap - swap + ] get-type preds>> [ Sum? ] count ] unit-test
{ 1 } [ [ [ + ] [ swap + ] if ] get-type preds>> [ Sum? ] count ] unit-test


! NOTE: those stupid drops are in there because otherwise we just
! get the wrapper type... meh FIXME should be fixed now
{ t } [ [ 1 drop 42 ] [ 40 2 + ] same-type? ] unit-test
{ t } [ [ 1 drop 42 ] [ 40 2 swap + ] same-type? ] unit-test
{ t } [ [ 1 drop 42 ] [ 44 2 - ] same-type? ] unit-test
{ f } [ [ 1 drop 42 ] [ 44 2 swap - ] same-type? ] unit-test
{ t } [ [ 1 drop 42 ] [ 6 7 * ] same-type? ] unit-test
{ t } [ [ 1 drop 6 ] [ 42 7 / ] same-type? ] unit-test
{ f } [ [ 1 drop 6 ] [ 7 42 / ] same-type? ] unit-test
{ t } [ [ 1 drop 7 ] [ 42 6 / ] same-type? ] unit-test

{ t } [ [ 1 + ] [ 4 - 5 + ] same-type? ] unit-test
{ t } [ [ 4 - 5 + ] [ 5 + 4 - ] same-type? ] unit-test
{ t } [ [ 4 - 8 - ]  [ 12 - ] same-type? ] unit-test
{ t } [ [ 3 - 8 + ]  [ 5 + ] same-type? ] unit-test
{ t } [ [ 8 + 3 - ]  [ 5 + ] same-type? ] unit-test
{ t } [ [ 8 - 3 + ]  [ 5 - ] same-type? ] unit-test
{ t } [ [ 3 + 8 - ]  [ 5 - ] same-type? ] unit-test
{ -7 } [ 0 4 - 8 - 5 + ] unit-test
{ t } [ [ 4 - 8 - 5 + ] [ 7 - ] same-type? ] unit-test
{ t } [ [ 4 - 8 - 5 + ] [ 4 - 5 + 8 - ] same-type? ] unit-test
{ t } [ [ 4 - 8 - 5 + ] [ 8 - 5 + 4 - ] same-type? ] unit-test
{ t } [ [ 5 + 8 - 4 - ] [ 8 - 5 + 4 - ] same-type? ] unit-test

{ t } [ [ 4 + 2 + ] [ 2 + 4 + ] same-type? ] unit-test
{ t } [ [ 4 + 2 + 4 - ] [ 2 + ] same-type? ] unit-test
{ t } [ [ 4 / 2 / ] [ 2 / 4 / ] same-type? ] unit-test
{ t } [ [ 2 / 4 / ] [ 8 / ] same-type? ] unit-test
{ t } [ [ 2 / 4 / 2 * ] [ 4 / ] same-type? ] unit-test

{ 4 } [ 16 2 / 4 / 2 * ]  unit-test
{ 4 } [ 16 2 * 4 / 2 / ] unit-test
{ 4 } [ 16 4 / 2 * 2 / ]  unit-test

{ t } [ [ 2 / 4 / 2 * ] [ 2 * 4 / 2 / ] same-type? ] unit-test
{ t } [ [ 2 * 4 / 2 / ] [ 4 / 2 * 2 / ] same-type? ] unit-test
{ t } [ [ 2 / 4 / 2 * ] [ 4 / 2 * 2 / ] same-type? ] unit-test

{ t }
[ [ callable? ] [ callable instance? ] same-type? ] unit-test

! FIXME: there's a slight impreciseness here, as for the first case, the instance of the
! value is not carried over.
P{ Xor
   ! P{ Effect L{ ?y2 . ?a1 } L{ ?z2 . ?a1 } f { P{ Instance ?z2 t } P{ Eq ?z2 t } P{ Eq ?y2 5 } P{ Instance ?y2 fixnum } } }
   P{ Effect L{ ?y2 . ?a1 } L{ ?z2 . ?a1 } f { P{ Instance ?z2 t } P{ Eq ?z2 t } P{ Eq ?y2 5 } } }
   P{ Effect L{ ?y . ?a4 } L{ ?z . ?a4 } f { P{ Instance ?z POSTPONE: f } P{ Eq ?z f } P{ Neq ?y 5 } } }
 } [ [ 5 = ] get-type ] chr-test

{ t }
[ [ + 5 = [ swap ] when ] get-type Xor? ] unit-test

P{ Effect L{ ?x . ?a } L{ ?y . ?a } f { P{ Instance ?x bignum } P{ Instance ?y fixnum }
                                        P{ Eq ?x ?y }
                                        P{ Le ?x $ most-positive-fixnum }
                                        P{ Le $ most-negative-fixnum ?x }
                                      } }
[ [ bignum>fixnum ] get-type ] chr-test

P{ Effect ?a L{ ?x3 ?x3 . ?a } f { P{ Instance ?x3 word } P{ Eq ?x3 swap } } }
[ [ \ swap dup ] get-type ] chr-test

SYMBOL: foo-sym
ALIAS: bar-sym foo-sym

! *** Eq
[ drop t ] [ dup eq? ] test-same-type

P{ Effect L{ ?x ?x . ?a } L{ ?x . ?a } f { P{ Instance ?x fixnum } } }
[ { fixnum } declare over eq? { t } declare drop ] test-chr-type

P{ Effect L{ ?x ?x . ?a } L{ ?x . ?a } f { P{ Instance ?x word } } }
[ { word union{ fixnum word } } declare over eq? { t } declare drop ] test-chr-type

P{ Effect L{ ?x ?x . ?a } L{ ?x . ?a } f { P{ Instance ?x array } } }
[ { array } declare over eq? { t } declare drop ] test-chr-type

[ t 1 ] [ { 42 } dup eq? 1 ] test-same-type
[ 1 drop f ] [ { 42 } { 42 } eq? ] test-same-type
[ 1 drop t ] [ 42 42 eq? ] test-same-type
[ 1 drop t ] [ f f eq? ] test-same-type
[ 1 drop t ] [ t t eq? ] test-same-type
[ 1 drop t ] [ foo-sym foo-sym eq? ] test-same-type
[ 1 drop t ] [ foo-sym bar-sym eq? ] test-same-type

! Not sure what that was supposed to test
! [ { 42 } { 42 } 2dup = [ eq? ] [ 2drop f ] if ] qt.

[ drop eq? ] [ [ eq? ] [ eq? ] if ] test-same-type
[ drop eq? ] [ [ swap eq? ] [ eq? ] if ] test-same-type

! Tracking eq through slots and potentially literal slots
TUPLE: foobox foobox-a foobox-b ;
{ 1 1 1 } [
    [ boa foobox-a>> ]
    get-type preds>>
    [ [ Slot? ] count ]
    [ [ LocPop? ] count ]
    [ [ PushLoc? ] count ] tri ] unit-test

[ { object object } declare drop ] [ foobox boa foobox-a>> ] test-same-type
[ nip ] [ foobox boa foobox-b>> ] test-same-type
[ foobox-a>> dup ] [ [ foobox-a>> ] [ foobox-a>> ] bi ] test-same-type

{ 1 1 1 } [
    [ dup foobox-a>> [ 42 >>foobox-a ] dip ]
    get-type preds>>
    [ [ Slot? ] count ]
    [ [ LocPop? ] count ]
    [ [ PushLoc? ] count ] tri ] unit-test

{ 1 1 1 } [
    [ boa dup foobox-a>> [ 42 >>foobox-a ] dip ]
    get-type preds>>
    [ [ Slot? ] count ]
    [ [ LocPop? ] count ]
    [ [ PushLoc? ] count ] tri ] unit-test

! NOTE: isomorphism checker chokes on this if we don't sanitize the state chains?
[ [ foobox-a>> ] keep foobox-b>> ] [ [ foobox-b>> ] keep foobox-a>> swap ] test-same-type
[ drop t ] [ dup foobox boa [ foobox-a>> ] [ foobox-b>> ] bi eq? ] test-same-type
[ t ] [ { 42 } dup foobox boa [ foobox-a>> ] [ foobox-b>> ] bi eq? ] test-same-type
[ t ] [ [ { 42 } dup foobox boa [ foobox-a>> ] [ foobox-b>> ] bi ] call eq? ] test-same-type
[ f ] [ [ { 42 } { 42 } foobox boa [ foobox-a>> ] [ foobox-b>> ] bi ] call [ eq? ] call ] test-same-type
[ f ] [ { 42 } { 42 } foobox boa [ foobox-a>> ] [ foobox-b>> ] bi eq? ] test-same-type
TUPLE: barbox { barbox-a read-only } { barbox-b read-only } ;
{ t } [ [ [ barbox-a>> ] [ barbox-b>> ] bi eq? ] get-type Xor? ] unit-test
[ 5 ] [ 5 dup barbox boa [ barbox-a>> ] call ] test-same-type
[ t ] [ { 42 } dup barbox boa [ barbox-a>> ] [ barbox-b>> ] bi eq? ] test-same-type
[ t ] [ [ { 42 } dup barbox boa [ barbox-a>> ] [ barbox-b>> ] bi ] call eq? ] test-same-type
[ f ] [ [ { 42 } { 42 } barbox boa [ barbox-a>> ] [ barbox-b>> ] bi ] call eq? ] test-same-type
[ t ] [ [ 5 5 barbox boa [ barbox-a>> ] [ barbox-b>> ] bi ] call eq? ] test-same-type

! Prove that a local allocation can only be eq? if it is the same var?
! Indirectly, by catching the case where local allocations can never
! appear in word inputs!
{ t } [ [ boa eq? ] get-type Xor? ] unit-test
[ 3drop f ] [ foobox boa eq? ] test-same-type
! ** Effectful access
! ro-slot access conversion

P{ Effect L{ ?o . ?a } L{ ?v . ?a } f
   { P{ Instance ?o cons-state }
     P{ Instance ?v object }
     P{ Slot ?o  T{ slot-spec { name "cdr" } { offset 3 } { class object } { read-only t } }
        ?v } } }
[ { cons-state } declare cdr>> ] test-chr-type

P{ Effect L{ ?y2 . ?ys2 } L{ ?v3 . ?ys2 } f
   { P{ Instance ?y2 curried } P{ Instance ?v3 object }
     P{ Slot ?y2
        T{ slot-spec { name "obj" } { offset 2 } { class object } { read-only t } }
        ?v3 } } }
[ { curried } declare obj>> ] test-chr-type

! insert check here that 2 slot hasn't been messed up!
P{
    Effect
    L{ ?o . ?a }
    L{ ?v . ?a }
    { ?x1 }
    {
        P{ Instance ?o not{ integer } }
        P{ Instance ?v object }
        P{ Slot ?o 2 ?x1 }
        P{ LocPop ?x1 ?a L{ ?v } ?a f ?a }
        P{ PushLoc ?x1 ?a L{ ?v } ?a f }
    }
}
[ [ { curried } declare obj>> ] qt [ 2 slot ] pick-type ] chr-test

[ { curried } declare obj>> ] [ { curried } declare 2 slot ] test-same-type

P{ Effect L{ ?y2 . ?ys2 } L{ ?v3 . ?ys2 } { ?x } {
        P{ Instance ?y2 curried-effect }
        P{ Instance ?v3 object }
        P{ Slot ?y2 T{ slot-spec { name "obj" } { offset 2 } { class object } } ?x }
        P{ PushLoc ?x ?ys2 L{ ?v3 } ?ys2 f }
        P{ LocPop ?x ?ys2 L{ ?v3 } ?ys2 f ?ys2 } } }
[ { curried-effect } declare obj>> ] test-chr-type

[ { curried-effect } declare obj>> ] [ { curried-effect } declare 2 slot ] test-same-type

! Effect must survive
P{ Effect L{ ?o1 ?v1 . ?a1 } ?c2 { ?x2 ?z2 ?b3 } {
        P{ Instance ?o1 not{ integer } }
        P{ Instance ?v1 object }
        P{ Slot ?o1 2 ?x2 }
        P{ PushLoc ?x2 ?b3 L{ ?v1 } ?c2 f }
        P{ LocPop ?x2 ?a1 L{ ?z2 } ?b3 f ?a1 } } }
[ 2 set-slot ] test-chr-type

! Local allocations, writeback should be ignored
P{ Effect ?a1 ?a1 f f }
[ 42 { 43 } 2 set-slot ] test-chr-type

P{ Effect L{ ?z . ?a } ?a f { P{ Instance ?z object } } }
[ 1array 42 swap 2 set-slot ] test-chr-type

! Flushable, thus can be ignored
! FIXME: not doing that, keeping volatile access semantics
! right now, but that's really not intended?
P{
    Effect L{ ?o3 . ?a } ?a { ?x1 ?v3 }
    {
        P{ Instance ?o3 not{ integer } }
        P{ Slot ?o3 2 ?x1 }
        P{ PushLoc ?x1 ?a L{ ?v3 } ?a f }
        P{ Instance ?v3 object }
        P{ LocPop ?x1 ?a L{ ?v3 } ?a f ?a } } }
[ [ 2 slot drop ] get-type ] chr-test

P{ Effect L{ ?v . ?a } ?a f { P{ Instance ?v object } } }
[ [ 1array 2 slot drop ] get-type ] chr-test

! *** Basic Array Manipulation

P{ Effect ?a1 L{ ?x2 . ?a1 } f { P{ LocalAllocation ?a1 ?x2 } P{ Eq ?x2 { 42 } } P{ Instance ?x2 array } } }
[ [ { 42 } [  ] curry ] call call ] test-chr-type

CONSTANT: obj1 { 42 }
[ $ obj1 dup ] [ $ obj1 dup [ ] curry swap [ ] curry [ call ] bi@ ] test-same-type
[ obj1 dup ] [ obj1 dup [ ] curry swap [ ] curry [ call ] bi@ ] test-same-type
[ $ obj1 dup ] [ [ $ obj1 dup [ ] curry swap [ ] curry ] call [ call ] bi@ ] test-same-type
[ obj1 dup ] [ [ obj1 dup [ ] curry swap [ ] curry ] call [ call ] bi@ ] test-same-type

[ t ] [ { 42 } dup [ ] curry swap [ ] curry [ call ] bi@ eq? ] test-same-type

! FIXME: this can only work if we choose to compact to a literal again...
{ f } [ [ 1 drop { 43 } ] [ { 42 } 43 over 2 set-slot ] same-type? ] unit-test

[ 1 drop { 43 } 2 slot ] [ { 42 } 43 over 2 set-slot 2 slot ] test-same-type
[ 1 drop { 43 } dup 2 slot ] [ { 42 } 43 over 2 set-slot dup 2 slot ] test-same-type

! ! TODO: this is really verbose right now...
! P{
!     Effect
!     ?a1
!     L{ ?v1 ?x1 . ?a1 }
!     f
!     { P{ Instance ?x1 array } P{ Instance ?v1 fixnum } P{ Eq ?v1 42 } P{ Eq ?x1 { 42 } }
!       P{ LocalAllocation ?a1 ?x1 } } }
[ 43 1array 42 over 2 set-slot dup 2 slot ] [ { 43 } 42 over 2 set-slot dup 2 slot ] test-same-type

! *** Some cloning class predicate stuff
P{ Effect ?a ?b f { P{ Invalid } } }
[ [ { array } declare (clone) { string } declare ] get-type ] chr-test

! FIXME
{  } [ (clone) 2 slot ] test-chr-type
{  } [ 1array (clone) ] test-chr-type

[ dup drop ] [ 1array (clone) 2 slot ] test-same-type
! NOTE: See caveat in ...primitives.factor!
[ 2drop f ] [ (clone) eq? ] test-same-type

! TODO: tests for actually specializing stuff over clone...

TUPLE: footuple barslot ;
P{
    Effect
    L{ ?o . ?a }
    L{ ?v . ?a }
    { ?x1 }
    {
        P{ Instance ?v object }
        P{ Instance ?o footuple }
        P{ Slot ?o T{ slot-spec { name "barslot" } { offset 2 } { class object } } ?x1 }
        P{ LocPop ?x1 ?a L{ ?v } ?a f ?a }
        P{ PushLoc ?x1 ?a L{ ?v } ?a f }
    }
}
[ barslot>> ] test-chr-type

! TODO: improve what to test for
{ t } [ [ barslot>> barslot>> ] get-type canonical? ] unit-test

P{ Effect L{ ?v . ?b3 } L{ ?o . ?b3 } { ?x3 } {
        P{ Slot ?o T{ slot-spec { name "barslot" } { offset 2 } { class object } } ?x3 }
        P{ Instance ?o footuple }
        P{ Instance ?v object }
        P{ LocalAllocation ?b3 ?o }
        P{ PushLoc ?x3 ?b3 L{ ?v } ?b3 t } } }
[ footuple boa ] test-chr-type

TUPLE: foo2 aslot { bslot read-only } ;

P{ Effect L{ ?o . ?a } L{ ?v . ?a } f { P{ Slot ?o T{ slot-spec { name "bslot" } { offset 3 } { class object } { read-only t } } ?v } P{ Instance ?v object } P{ Instance ?o foo2 } } }
[ bslot>> ] test-chr-type

[ 42 ] [ T{ foo2 f 42 88 } aslot>> ] test-same-type
[ 88 ] [ T{ foo2 f 42 88 } bslot>> ] test-same-type

! { P{ Imply { ?o } { ?v } } }
! [ { ?o } P{ Slot ?o "bslot" ?v } imply-def ] unit-test

P{ Effect L{ ?x . ?a } L{ ?z . ?a } { ?y } {
       P{ Instance ?y foo2 }
       P{ Instance ?x foo2 }
       P{ Slot ?x T{ slot-spec { name "bslot" } { offset 3 } { class object } { read-only t } } ?y }
       P{ Slot ?y T{ slot-spec { name "bslot" } { offset 3 } { class object } { read-only t } } ?z }
       P{ Instance ?z object }
   }
 } [ [ bslot>> bslot>> ] get-type ] chr-test

[ 42 ] [ 42 f foo2 boa f foo2 boa aslot>> aslot>> ] test-same-type
[ 42 ] [ [ 42 f foo2 boa f foo2 boa ] call [ aslot>> aslot>> ] call ] test-same-type
[ 42 ] [ T{ foo2 f T{ foo2 f 42 f } f } aslot>> aslot>> ] test-same-type

[ 42 ] [ f 42 foo2 boa f swap foo2 boa bslot>> bslot>> ] test-same-type
[ 42 ] [ [ f 42 foo2 boa f swap foo2 boa ] call [ bslot>> bslot>> ] call ] test-same-type

[ 42 43 ] [ T{ foo2 f 42 43 } [ aslot>> ] [ bslot>> ] bi ] test-same-type
[ 43 42 ] [ T{ foo2 f 42 43 } [ bslot>> ] [ aslot>> ] bi ] test-same-type

! FIXME not losing internal predicates when unboa-allocation rule is not used!
[ 42 ] [ T{ foo2 f 42 } bslot>> ] test-same-type
[ 42 ] [ T{ foo2 f f T{ foo2 f f 42 } } bslot>> bslot>> ] test-same-type

TUPLE: foo3 slot1 slot2 ;
[ 42 33 ] [ 22 33 foo3 boa 42 >>slot1 [ slot1>> ] [ slot2>> ] bi ] test-same-type
[ 42 69 ] [ 22 33 foo3 boa 42 >>slot1 69 >>slot2 [ slot1>> ] [ slot2>> ] bi ] test-same-type
[ 42 69 ] [ 22 33 foo3 boa 69 >>slot2 42 >>slot1 [ slot1>> ] [ slot2>> ] bi ] test-same-type
[ 69 42 ] [ 22 33 foo3 boa 69 >>slot2 42 >>slot1 [ slot2>> ] [ slot1>> ] bi ] test-same-type


! *** Infinite Structures

! Setting an array's first element to itself, dereferencing
! That's a pretty interesting case, because it actually results in a hybrid literal structure
! being created, as in P{ Eq ?x11 { ?x11 } }, which is neither a factor literal, not a type variable.
! Looks cool because it seems we get recursive structure prototypes for free?
! This one only works as long as no specialized slots are involved
[ { 42 } dup dup 2 set-slot 2 slot ]
[ [ { 42 } dup dup 2 set-slot 2 slot ] call 2 slot ] test-same-type

[ { 42 } dup dup 2 set-slot 2 slot ]
[ { 42 } dup dup 2 set-slot 2 slot 2 slot ] test-same-type

! TODO: test that eq? is reasoned

! This one should work for all kind of data, as it describes the structure (construction)
! rather than building the literal
[ 1array dup dup 2 set-slot 2 slot ]
[ 1array dup dup 2 set-slot 2 slot 2 slot ] test-same-type

! ** Read-only locals

{ 1 } [ [ + load-local ] get-type preds>> [ Sum? ] count ] unit-test
{ 1 } [ [ 0 get-local + ] get-type preds>> [ Sum? ] count ] unit-test
{ 1 } [ [ 0 get-local -1 get-local + ] get-type preds>> [ Sum? ] count ] unit-test

{ t } [ [ swap ] [| a b | b a ] same-type? ] unit-test
{ t } [ [ swap ] [| | :> a :> b a b ] same-type? ] unit-test
[ swap swap drop ] [| | :> a :> b b ] test-same-type
[ swap swap drop ] [| a b | a ]  test-same-type
[ nip ] [| a b | b ] test-same-type
[ nip ] [| | :> a :> b a ] test-same-type
{ t } [ [ + ] [| a b | a b + :> c c ] same-type? ] unit-test
{ t } [ [ + dup ] [ [ [| | :> a a + ] [ dup ] compose ] call call ] same-type? ] unit-test

! *** With local write access
P{ Effect L{ ?o . ?a } L{ ?x2 ?x1 ?o . ?a } f
   { P{ Eq ?x1 42 } P{ Eq ?x2 43 } P{ Instance ?o object } P{ Instance ?x1 fixnum } P{ Instance ?x2 fixnum } } }
[| x | x 1array :> a a 2 slot 42 a 2 set-slot a 2 slot 43 a 2 set-slot a 2 slot ] test-chr-type

! ** Mutable locals

P{ Effect L{ ?v . ?a } L{ ?v . ?a } f { P{ Instance ?v object } } }
[ [| | :> a! a ] get-type ] chr-test

P{ Effect L{ ?v . ?a } ?a  f { P{ Instance ?v object } } }
[ [| | :> a! ] get-type ] chr-test

P{ Effect L{ ?v ?w . ?a } L{ ?w ?v . ?a }  f { P{ Instance ?v object } P{ Instance ?w object } } }
[ [| a! b! | b :> c a b! c a! a b ] get-type ] chr-test

P{ Effect L{ ?y . ?a } L{ ?y ?y . ?a } f { P{ Instance ?y object } } }
[ [ { 43 } over over 2 set-slot 2 slot ] get-type ] chr-test

P{ Effect L{ ?x . ?a } L{ ?x ?x . ?a } f { P{ Instance ?x object } } }
[| a! | a a ] test-chr-type

P{ Effect L{ ?x . ?a } L{ ?x ?x ?x . ?a } f { P{ Instance ?x object } } }
[| a! | a a a ] test-chr-type

P{ Effect L{ ?x . ?a } L{ ?x ?x ?x ?x . ?a } f { P{ Instance ?x object } } }
[| a! | a a a a ] test-chr-type

P{ Effect L{ ?x . ?a } L{ ?x ?x ?x ?x ?x . ?a } f { P{ Instance ?x object } } }
[| a! | a a a a a ] test-chr-type

P{
    Effect
    L{ ?o . ?a }
    L{ ?v ?v ?v ?v . ?a }
    { ?x }
    {
        P{ Instance ?o not{ integer } }
        P{ Instance ?v object }
        P{ SlotLoc ?x ?o 2 }
        P{ PushLoc ?x ?a L{ ?v } ?a f }
        P{ LocPop ?x ?a L{ ?v } ?a f __ }
    }
}
[| | :> a a 2 slot a 2 slot a 2 slot a 2 slot ] test-chr-type

[ dup drop + ] [ dup 2 = [ + ] [ + ] if ] test-same-type

[ drop ] [ 1array 2 slot drop ] test-same-type

[ drop ] [ 1array 43 swap 2 set-slot ] test-same-type

[ 1 drop f ] [ { 42 } { 42 } eq? ] test-same-type

{ 1 1 1 }
[ [ 1array 42 over 2 set-slot dup 2 slot over 2 slot ] get-type
  preds>>
  [ [ SlotLoc? ] count ]
  [ [ PushLoc? ] count ]
  [ [ LocalAllocation? ] count ] tri
] unit-test

[ drop 42 dup ] [ 1array 42 over 2 set-slot dup 2 slot swap 2 slot ] test-same-type

[ drop 1 ] [ footuple boa drop 1 ] test-same-type

[ 1 drop 42 ] [ { { 42 } } array-first array-first ] test-same-type

[ 1 drop 42 ] [ T{ footuple f 42 } barslot>> ] test-same-type

P{ Effect ?a L{ ?v . ?a } f { P{ Instance ?v array } P{ Eq ?v { 42 } } P{ LocalAllocation ?a ?v } } }
[ T{ footuple f { 42 } } barslot>> ] test-chr-type

[ 1 drop 42 ] [ T{ footuple f T{ footuple f 42 } } barslot>> barslot>> ] test-same-type

! ** Nested local allocations
{ t } [ [ 1array ] [ 1array 1array 2 slot ] same-type? ] unit-test

P{ Effect L{ ?v . ?a } L{ ?v . ?a } f { P{ Instance ?v object } } }
[ [ 1array 1array 2 slot 2 slot ] get-type ] chr-test

P{ Effect L{ ?v . ?a } ?a  f { P{ Instance ?v object } } }
[ [ 1array 1array 2 slot 2 slot drop ] get-type ] chr-test

! ** TODO Effectful Predicates Phi

[ drop 2 slot ] [ [ 2 slot ] [ 2 slot ] if ] test-same-type
[ drop 2 slot 2 slot ] [ [ 2 slot 2 slot ] [ 2 slot 2 slot ] if ] test-same-type
! FIXME
[ drop 2 slot 2 slot ] [ [ 2 slot 2 slot ] [ 2 slot ] if ] test-same-type

! ** Simple Dispatch
GENERIC: foothing ( obj -- result )
M: fixnum foothing 3 + ;
M: array foothing array-first ;

! FIXME
CONSTANT: foothing1
P{ Effect L{ ?y . ?c } L{ ?z . ?c } f { P{ Instance ?y fixnum } P{ Instance ?z integer } P{ Sum ?z ?y 3 } } }

! Note: extra stuff because need to expand to the call type
foothing1
[ M\ fixnum foothing 1quotation [ call ] curry get-type ] chr-test

! FIXME
CONSTANT: foothing2
P{
    Effect L{ ?o . ?a } L{ ?v . ?a } { ?x ?b } {
        P{ Instance ?o array }
        P{ Instance ?v object }
        P{ SlotLoc ?x ?o 2 }
        P{ PushLoc ?x ?b L{ ?v } ?a f }
        P{ LocPop ?x ?a L{ ?v } ?b f ?a } } }

foothing2
[ M\ array foothing 1quotation [ call ] curry get-type ] chr-test

P{ Xor $ foothing2 $ foothing1 }
[ \ foothing get-type ] chr-test

P{ Effect L{ ?o . ?a } L{ ?v . ?a } f
   { P{ Instance ?v object } P{ Instance ?o cons-state } P{ Slot ?o "cdr" ?v } } }
[ [ cdr>> ] get-type ] chr-test

! ** Overlapping dispatch
GENERIC: auto-dispatch ( obj -- res )
M: list auto-dispatch cdr>> ;
M: +nil+ auto-dispatch ;
M: object auto-dispatch ;

! ! REM, since dispatch expansion does this calculation on the fly
! { { L{ } cons-state intersection{ not{ cons-state } not{ L{ } } } } }
! [ \ auto-dispatch dispatch-method-seq keys ] unit-test

P{
    Xor
    P{ Effect L{ ?y2 . ?ys2 } L{ ?y2 . ?ys2 } f { P{ Instance ?y2 not{ cons-state } } } }
    P{ Effect L{ ?o4 . ?a43 } L{ ?v . ?a43 } f { P{ Instance ?o4 cons-state } P{ Slot ?o4 "cdr" ?v } P{ Instance ?v object } } }
}
[ \ auto-dispatch get-type ] chr-test

: manual-dispatch ( obj -- res )
    dup +nil+? [ ]
    [ dup list? [ cdr>> ] [ ] if ] if ;

{ 42 } [ 42 manual-dispatch ] unit-test
{ L{ 42 } } [ L{ 43 42 } manual-dispatch ] unit-test
{ +nil+ } [ L{ } manual-dispatch ] unit-test

P{
    Xor
    P{ Effect L{ ?x1 . ?rho1 } L{ ?x1 . ?rho1 } f { P{ Instance ?x1 not{ cons-state } } } }
    P{
        Effect
        L{ ?x2 . ?rho2 }
        L{ ?v1 . ?rho2 }
        f
        { P{ Instance ?x2 cons-state } P{ Slot ?x2 "cdr" ?v1 } P{ Instance ?v1 object } }
    }
}
[ \ manual-dispatch get-type ] chr-test


{ t } [ \ auto-dispatch \ manual-dispatch same-type? ] unit-test


GENERIC: default-dispatch ( obj -- res )
M: list default-dispatch cdr>> ;
M: +nil+ default-dispatch ;

P{
    Xor
    P{ Effect L{ ?y1 . ?ys1 } L{ ?y1 . ?ys1 } f { P{ Instance ?y1 L{ } } P{ Eq ?y1 L{ } } } }
    P{ Effect L{ ?o1 . ?a1 } L{ ?v . ?a1 } f { P{ Instance ?o1 cons-state } P{ Slot ?o1 "cdr" ?v } P{ Instance ?v object } } }
}
[ \ default-dispatch get-type ] chr-test

! ** Single recursion
: myloop ( -- ) [ call ] keep swap [ myloop ] [ drop ] if ; inline recursive

{ t } [ [ myloop ] get-type dup [ full-type? ] when ] unit-test

! :)
! FIXME works but extremely slow isomorphism test
! :(
! { t }
! [ [ myloop ] [ loop ] same-type? ] unit-test

P{ Effect ?a ?b f { P{ Invalid } } } [ [ [ t ] loop ] get-type ] chr-test
P{ Effect ?a ?b f { P{ Invalid } } } [ [ [ t ] myloop ] get-type ] chr-test

: indirect-loop ( x -- y ) dup 0 > [ 1 - [ indirect-loop ] call ] when ;

! FIXME: better test?
{ t } [ [ [ indirect-loop ] call ] get-type canonical? ] unit-test


! ** Nested loop inference
: inner-loop ( x -- y ) dup 0 > [ 1 - inner-loop ] when ;
: outer-loop ( x -- y ) dup inner-loop drop dup 0 > [ 1 - outer-loop ] when ;

CONSTANT: dumb-loop
P{
    Xor
    P{ Effect L{ ?x1 . ?a1 } L{ ?y1 . ?a1 } f { P{ Le ?y1 0 } P{ Instance ?y1 number } P{ Lt 0 ?x1 } P{ Instance ?x1 number } } }
    P{ Effect L{ ?x2 . ?a2 } L{ ?x2 . ?a2 } f { P{ Le ?x2 0 } P{ Instance ?x2 number } } }
}

dumb-loop [ [ [ dup 0 > [ 1 - t ] [ f ] if ] loop ] get-type ] chr-test

dumb-loop [ [ inner-loop ] get-type ] chr-test

dumb-loop [ [ outer-loop ] get-type ] chr-test

! ** Mutually recursive definitions

: chr-error ( quot -- quot )
    '[ dup chr-inference-error? [ error>> @ ] [ drop f ] if ] ;

! Must fail
DEFER: pong
: ping ( x -- x ) pong ;
: pong ( x -- x ) ping ;

[ [ ping ] get-type ] [ no-recursive-fixpoint? ] chr-error must-fail-with

DEFER: peng
: pang ( x -- x ) peng ;
: peng ( x -- x ) dup 0 > [ 1 - pang ] when ;

dumb-loop [ [ pang ] get-type ] chr-test
dumb-loop [ [ peng ] get-type ] chr-test

! Must fail
DEFER: ipong
: iping ( x -- x ) [ ipong ] call ;
: ipong ( x -- x ) [ iping ] call ;

[ [ iping ] get-type ] [ no-recursive-fixpoint? ] chr-error must-fail-with
[ [ [ iping ] call ] get-type ] [ no-recursive-fixpoint? ] chr-error must-fail-with


! Must infer as same type
DEFER: ipeng
: ipang ( x -- x ) [ [ ipeng ] call ] call ;
: ipeng ( x -- x ) dup 0 > [ 1 - [ ipang ] call ] when ;


! { t } [ [ ipang ] [ ipeng ] same-type? ] unit-test
dumb-loop [ [ ipang ] get-type ] chr-test
dumb-loop [ [ ipeng ] get-type ] chr-test


! TODO: test more subtle cases of non-termination

GENERIC: lastfail1 ( x -- x )
M: array lastfail1 array-first lastfail1 ;

[ [ lastfail1 ] get-type ] [ no-recursive-fixpoint? ] chr-error must-fail-with
[ M\ array lastfail1 get-type ] [ no-recursive-fixpoint? ] chr-error must-fail-with

GENERIC: lastfail2 ( x -- x )
M: array lastfail2 array-first lastfail2 ;
M: list lastfail2 cdr>> lastfail2 ;

[ [ lastfail2 ] get-type ] [ no-recursive-fixpoint? ] chr-error must-fail-with
[ M\ array lastfail2 get-type ] [ no-recursive-fixpoint? ] chr-error must-fail-with
[ M\ list lastfail2 get-type ] [ no-recursive-fixpoint? ] chr-error must-fail-with

! FIXME progress!
GENERIC: nonlastfail3 ( x -- x )
M: array nonlastfail3 array-first [ nonlastfail3 ] call ;
M: list nonlastfail3 cdr>> [ [ nonlastfail3 ] call ] call ;
M: +nil+ nonlastfail3 ;

! FIXME: better test
{ t } [ [ nonlastfail3 ] get-type canonical? ] unit-test

! Similar to above but explicit
DEFER: ind3-dispatch
DEFER: ind3-array
: ind3-nil ( x -- x ) { L{  } } declare ;
! : ind3-list ( x -- x ) { list } declare cdr>> ind3-dispatch ;
! : ind3-array ( x -- x ) { array } declare array-first ind3-dispatch ;
: ind3-list ( x -- x ) { list } declare cdr>> dup +nil+? [ ind3-nil ] [ dup list? [ ind3-list ] [ dup array? [ ind3-array ] [ "nope" throw ] if ] if ] if ;
: ind3-array ( x -- x ) { array } declare array-first dup +nil+? [ ind3-nil ] [ dup list? [ ind3-list ] [ dup array? [ ind3-array ] [ "nope" throw ] if ] if ] if ;

! : ind3-dispatch ( x -- x )
!     dup +nil+? [ ind3-nil ]
!     [ dup list? [ ind3-list ]
!       [ dup array? [ ind3-array ]
!         [ "nope" throw ] if
!       ] if
!     ] if ;

{ t } [ [ ind3-list ] get-type canonical? ] unit-test

GENERIC: lastfail3 ( x -- x )
M: array lastfail3 array-first [ lastfail3 ] call ;
! M: list lastfail3 cdr>> [ [ lastfail3 ] ] call call ;
! v that one's the evil one!
M: list lastfail3 cdr>> [ [ lastfail3 ] call ] call ;
! M: footuple lastfail3 barslot>> [ [ lastfail3 ] call ] call ;
! M: footuple lastfail3 barslot>> [ [ lastfail3 ] ] call call ;

! FIXME
[ [ lastfail3 ] get-type ] [ no-recursive-fixpoint? ] chr-error must-fail-with
[ M\ array lastfail3 get-type ] [ no-recursive-fixpoint? ] chr-error must-fail-with
[ M\ list lastfail3 get-type ] [ no-recursive-fixpoint? ] chr-error must-fail-with
! [ M\ footuple lastfail3 get-type ] [ no-recursive-fixpoint? ] must-fail-with

CONSTANT: sol4 P{ Xor
                  P{ Effect L{ ?x1 . ?a1 } L{ ?x2 . ?a1 } f { P{ Instance ?x2 L{ } } P{ Eq ?x2 L{ } } P{ Instance ?x1 union{ cons-state array } } } }
                  P{ Effect L{ ?x3 . ?a2 } L{ ?x3 . ?a2 } f { P{ Instance ?x3 L{ } } P{ Eq ?x3 L{ } } } } }

GENERIC: mylastcdr ( list -- obj )
M: list mylastcdr
    cdr>> [ [ mylastcdr ] ] (call) (call) ; ! Doesnt work so well...
M: +nil+ mylastcdr ;
M: array mylastcdr array-first [ [ mylastcdr ] (call) ] (call) ;
! M: array mylastcdr array-first [ [ mylastcdr ] (call) ] (call) ;

sol4 [ [ mylastcdr ] get-type ] chr-test

! Same as lastcdr1, but as single word
: lastfoo1 ( x -- x )
    dup +nil+? [  ]
    [ dup list? [ cdr>> lastfoo1 ] [ "nope" throw ] if
    ] if ;
{ L{ } } [ L{ } lastfoo1 ] unit-test
{ L{ } } [ L{ 1 2 3 } lastfoo1 ] unit-test
[ L{ 1 2 3 . 4 } lastfoo1 ] [ "nope" = ] must-fail-with
[ 42 lastfoo1 ] [ "nope" = ] must-fail-with

P{ Xor
    P{ Effect L{ ?x1 . ?a1 } L{ ?x2 . ?a1 } f { P{ Instance ?x1 cons-state } P{ Eq ?x2 L{ } } P{ Instance ?x2 L{ } } } }
    P{ Effect L{ ?x3 . ?a2 } L{ ?x3 . ?a2 } f { P{ Instance ?x3 L{ } } P{ Eq ?x3 L{ } } } }
 } [ [ lastfoo1 ] get-type ] chr-test

GENERIC: lastcdr1 ( list -- obj )
M: list lastcdr1 cdr>> lastcdr1 ;
M: +nil+ lastcdr1 ;

{ f } [ object \ lastcdr1 dispatch-method-seq constrains-methods? ] unit-test
{ t } [ +nil+ \ lastcdr1 dispatch-method-seq constrains-methods? ] unit-test
! FIXME?
{ f } [ list \ lastcdr1 dispatch-method-seq constrains-methods? ] unit-test
{ f } [ object \ length dispatch-method-seq constrains-methods? ] unit-test
{ f } [ sequence \ length dispatch-method-seq constrains-methods? ] unit-test
{ t } [ array \ length dispatch-method-seq constrains-methods? ] unit-test

! This must have the same type when inferred on [ lastcdr1 ] !
P{ Effect L{ ?x . ?a } L{ ?b . ?a } f { P{ Instance ?x cons-state } P{ Eq ?b L{ } } P{ Instance ?b L{ } } } }
[ M\ list lastcdr1 get-type ] chr-test

CONSTANT: sol1
P{
    Xor
    P{ Effect L{ ?y1 . ?ys1 } L{ ?y1 . ?ys1 } f { P{ Instance ?y1 L{ } } P{ Eq ?y1 L{ } } } }
    ! Finally able to infer the resolved recursion type...
    P{ Effect L{ ?x . ?a } L{ ?y . ?a } f { P{ Instance ?x cons-state } P{ Instance ?y L{ } } P{ Eq ?y L{ } } } }
    ! P{ Effect L{ ?o3 . ?a15 } ?b4 f { P{ CallRecursive __ ?a15 ?b4 } } }
}

sol1
[ [ lastcdr1 ] get-type ] chr-test

{ t }
[ [ lastcdr1 ] [ 1 drop lastcdr1 ] same-type? ] unit-test

{ t } [ [ lastcdr1 ] [ lastfoo1 ] same-type? ] unit-test


GENERIC: lastcdr2 ( list -- obj )
M: list lastcdr2 cdr>> [ lastcdr2 ] (call) ;
M: +nil+ lastcdr2 ;

sol1
[ [ lastcdr2 ] get-type ] chr-test

GENERIC: lastcdr3 ( list -- obj )
M: list lastcdr3 cdr>> [ [ lastcdr3 ] ] (call) (call) ;
M: +nil+ lastcdr3 ;

sol1
[ [ lastcdr3 ] get-type ] chr-test

sol1
[ [ [ lastcdr3 ] (call) ] get-type ] chr-test

sol1
[ [ [ [ lastcdr3 ] ] (call) (call) ] get-type ] chr-test

! Multiple (tail-recursive) call sites
: lastfoo4 ( list -- obj )
    dup +nil+? [ ]
    [ dup list? [ cdr>> lastfoo4 ]
      [ dup array? [ array-first [ lastfoo4 ] (call) ]
        [ "nope" throw ] if
      ] if
    ] if ;

sol4 [ [ lastfoo4 ] get-type ] chr-test

! FIXME: maybe reactivate if a bit quicker?
! { t } [ [ [ lastfoo4 ] ] get-type canonical? ] chr-test

! sol4 [ [ [ lastfoo4 ] (call) ] get-type ] chr-test

GENERIC: lastcdr4 ( list -- obj )
M: list lastcdr4 cdr>> [ [ lastcdr4 ] ] (call) (call) ;
M: +nil+ lastcdr4 ;
M: array lastcdr4 array-first lastcdr4 ;

sol4 [ [ lastcdr4 ] get-type ] chr-test

sol4 [ [ lastcdr4 dup drop ] get-type ] chr-test
sol4 [ [ [ lastcdr4 ] (call) ] get-type ] chr-test

DEFER: lastfoo-dispatch

: lastfoo-nil ( x -- x )
    { +nil+ } declare ;
: lastfoo-list ( x -- x )
    { list } declare cdr>> lastfoo-dispatch ;
: lastfoo-array ( x -- x )
    { array } declare array-first lastfoo-dispatch ;

: lastfoo-dispatch ( x -- x )
    dup +nil+? [ lastfoo-nil ]
    [ dup list? [ lastfoo-list ]
      [ dup array? [ lastfoo-array ]
        [ "nope" throw ]
        if ]
      if ]
    if ;

CONSTANT: sol5 P{ Xor
    P{ Effect L{ ?x1 . ?a1 } L{ ?x1 . ?a1 } f { P{ Eq ?x1 L{ } } P{ Instance ?x1 L{ } } } }
    P{
        Effect
        L{ ?x2 . ?a2 }
        L{ ?x3 . ?a2 }
        f
        { P{ Instance ?x3 L{ } } P{ Eq ?x3 L{ } } P{ Instance ?x2 union{ cons-state array } } } } }


sol5 [ [ lastfoo-dispatch ] get-type ] chr-test

DEFER: lastfoo5-dispatch

: lastfoo5-tuple ( x -- x )
    { footuple } declare barslot>> lastfoo5-dispatch ;
: lastfoo5-nil ( x -- x )
    { +nil+ } declare ;
: lastfoo5-list ( x -- x )
    { list } declare cdr>> lastfoo5-dispatch ;
: lastfoo5-array ( x -- x )
    { array } declare array-first lastfoo5-dispatch ;

: lastfoo5-dispatch ( x -- x )
    dup +nil+? [ lastfoo5-nil ]
    [ dup list? [ lastfoo5-list ]
      [ dup array? [ lastfoo5-array ]
        [ dup footuple? [ lastfoo5-tuple ]
          [ "nope" throw ] if ]
        if ]
      if ]
    if ;

! TODO: add test which goes through more levels of nesting

{ t } [ [ lastfoo5-dispatch ] get-type canonical? ] unit-test
{ t } [ [ lastfoo5-list ] get-type canonical? ] unit-test

GENERIC: lastcdr5 ( list -- obj )
M: list lastcdr5 cdr>> lastcdr5 ;
M: +nil+ lastcdr5 ;
M: array lastcdr5 array-first lastcdr5 ;

sol5 [ [ lastcdr5 ] get-type ] chr-test


! (old)NOTE: This one does not work because we don't recursively perform full phi-computations
! through multiple levels of nested effects (yet?)
! (update) Fixed by not phi-merging anything to do with unresolved computations
{ t } [ [ [ lastcdr5 ] ] [ [ [ lastcdr5 ] ] (call) ] same-type? ] unit-test


! NOTE: this one has two loop exit branches!
: lastfoo6 ( x -- x )
    dup +nil+? [  ]
    [ dup list? [ cdr>> lastfoo6 ] when
    ] if ;

{ +nil+ } [ L{ 12 } lastfoo6 ] unit-test
{ 42 } [ L{ 12 . 42 } lastfoo6 ] unit-test
{ 43 } [ 43 lastfoo6 ] unit-test

CONSTANT: sol6 P{ Xor
    P{ Effect L{ ?y2 . ?ys2 } L{ ?y2 . ?ys2 } f { P{ Instance ?y2 not{ cons-state } } } }
    P{ Effect L{ ?x . ?a } L{ ?y . ?a } f { P{ Instance ?x cons-state } P{ Instance ?y not{ cons-state } } } } }

sol6 [ [ lastfoo6 ] get-type ] chr-test

! Correct one
GENERIC: lastcdr6 ( list -- obj )
M: list lastcdr6 cdr>> lastcdr6 ;
M: +nil+ lastcdr6 ;
M: object lastcdr6 ;

{ +nil+ } [ L{ 12 } lastcdr6 ] unit-test
{ 42 } [ L{ 12 . 42 } lastcdr6 ] unit-test
{ 43 } [ 43 lastcdr6 ] unit-test

sol6 [ [ lastcdr6 ] get-type ] chr-test

! With array exception
GENERIC: lastcdr7 ( list -- obj )
M: list lastcdr7 cdr>> lastcdr7 ;
M: array lastcdr7 array-first lastcdr7 ;
M: +nil+ lastcdr7 ;
M: object lastcdr7 ;

CONSTANT: sol7 P{ Xor
    P{ Effect L{ ?y14 . ?ys14 } L{ ?y14 . ?ys14 } f { P{ Instance ?y14 intersection{ not{ cons-state } not{ array } } } } }
    P{
        Effect L{ ?o25 . ?a85 } L{ ?x17 . ?a85 } f
        { P{ Instance ?x17 intersection{ not{ cons-state } not{ array } } } P{ Instance ?o25 union{ cons-state array } } } } }

sol7 [ [ lastcdr7 ] get-type ] chr-test

! Same as lastcdr7, but as single word
: lastfoo7 ( x -- x )
    dup +nil+? [  ]
    [ dup list? [ cdr>> lastfoo7 ]
      [ dup array? [ array-first lastfoo7 ]
        [  ] if
      ] if
     ] if ;

sol7 [ [ lastfoo7 ] get-type ] chr-test

! Stack checker examples
: bad ( ? quot: ( ? -- ) -- ) 2dup [ not ] dip bad call ; inline recursive
: good ( ? quot: ( ? -- ) -- ) [ good ] 2keep [ not ] dip call ; inline recursive

! ** Basic Mutual Recursion

DEFER: tock
! : tick ( x -- y ) 1 - tock ;
! : tock ( x -- y ) dup 0 <= [ tick ] unless ;
! : tock ( x -- y ) dup 0 <= [ tick ] unless ;
: tick ( x -- y ) dup 0 <= [ 1 - tock ] unless ;
: tock ( x -- y ) dup 0 <= [ 1 - tick ] unless ;

{ t t }
[ [ tick tock ] qt
  [ [ tick ] pick-type ]
  [ [ tock ] pick-type ] bi
  [ [ canonical? ] keep ] dip
  same-effect?
] unit-test

DEFER: tac
: tic ( x -- y ) dup 0 <= [ 1 - tac ] unless ;
DEFER: toe
: tac ( x -- y ) dup 0 <= [ 1 - toe ] unless ;
: toe ( x -- y ) dup 0 <= [ 1 - tic ] unless ;

{ t t }
[ [ tic tac toe ] qt
  { [ tic ] [ tac ] [ toe ] } [ pick-type ] with map
  [ first canonical? ] keep
  [ same-effect? ] monotonic?
] unit-test

DEFER: itac
: itic ( x -- y ) dup 0 <= [ 1 - [ [ itac ] ] call call ] unless ;
DEFER: itoe
: itac ( x -- y ) dup 0 <= [ 1 - [ [ itoe ] ] call call ] unless ;
: itoe ( x -- y ) dup 0 <= [ 1 - [ [ itic ] ] call call ] unless ;

{ t t }
[ [ itic itac itoe ] qt
  { [ itic ] [ itac ] [ itoe ] } [ pick-type ] with map
  [ first canonical? ] keep
  [ same-effect? ] monotonic?
] unit-test


DEFER: tok
: tik-tik ( x -- y ) 2 - tok ;
: tok ( x -- y ) 1 + dup 0 <= [ tik-tik ] unless ;

P{ Effect L{ ?x . ?a } L{ ?y . ?a } f { P{ Instance ?x number } P{ Instance ?y number } P{ Le ?y 0 } } }
[ [ tik-tik ] get-type ] chr-test

{ t } [ [ tik-tik ] [ 1 drop tik-tik ] same-type? ] unit-test
{ t } [ [ tik-tik ] [ tok ] same-type? ] unit-test

! ** Macro expansion
MACRO: my-add1 ( num -- quot )
    [ + ] curry ;

{ 42 } [ 41 1 my-add1 ] unit-test

P{ Effect L{ ?a1 . ?i1 } ?o1 { ?q1 } {
       P{ MacroCall [ [ + ] curry ] { ?a1 } ?q1 }
       P{ Instance ?q1 callable }
       P{ CallEffect ?q1 ?i1 ?o1 }
   }
 }
[ [ my-add1 ] get-type ] chr-test

MACRO: my-add2 ( num -- quot )
    [ + 1 + ] curry ;

{ 43 } [ 41 1 my-add2 ] unit-test


P{ Effect L{ ?a1 . ?i1 } L{ ?z1 . ?i1 } f {
       P{ Instance ?a1 number }
       P{ Instance ?z1 number }
       P{ Sum ?z1 ?a1 1 }
   }
 }
[ [ 1 my-add1 ] get-type ] chr-test


P{ Effect L{ ?a1 . ?i1 } ?o4 { ?q2 ?a4 ?i4 ?q1 } {
       P{ MacroCall [ [ + ] curry ] { ?a1 } ?q1 }
       P{ Instance ?q1 callable }
       P{ CallEffect ?q1 ?i1 L{ ?a4 . ?i4 } }
       P{ MacroCall [ [ + 1 + ] curry ] { ?a4 } ?q2 }
       P{ Instance ?q2 callable }
       P{ CallEffect ?q2 ?i4 ?o4 }
   }
 }
[ [ my-add1 my-add2 ] get-type ] chr-test

P{ Effect L{ ?a1 . ?i1 } L{ ?z1 . ?i1 } f ! { ?z6 }
   {
       P{ Instance ?a1 number }
       P{ Instance ?z1 number }
       P{ Sum ?z1 ?a1 4 }
       ! P{ Sum ?z1 ?z6 1 }
       ! P{ Instance ?z6 number }
       ! P{ Sum ?z6 ?a1 3 }
   }
 }
[ [ 1 2 my-add1 my-add2 ] get-type ] chr-test


P{ Effect L{ ?a1 . ?i1 } ?o4 { ?a4 ?q2 } {
       P{ Instance ?a1 number }
       P{ MacroCall [ [ + 1 + ] curry ] { ?a4 } ?q2 }
       P{ Instance ?a4 number }
       P{ Sum ?a4 ?a1 1 }
       P{ Instance ?q2 callable }
       P{ CallEffect ?q2 ?i1 ?o4 }
   }
 }
[ [ 1 my-add1 my-add2 ] get-type ] chr-test

! P{ Effect L{ ?a1 . ?i1 } L{ ?z1 . ?i1 } { ?z6 } {
!        P{ Instance ?a1 number }
!        P{ Instance ?z1 number }
!        P{ Sum ?z1 ?z6 1 }
!        P{ Instance ?z6 number }
!        P{ Sum ?z6 ?a1 3 }
!    }
!  }
! [ [ 1 my-add1 dup 99 my-add2 ] get-type ] chr-test

! Macros with conditionals

MACRO: my-mux ( cond -- quot )
    [ not [ swap ] when drop ] curry ;

{ 1 2 } [ 1 2 [ t my-mux ] [ f my-mux ] 2bi ] unit-test

! NOTE: this is something the current stack checker can not do
{ t } [ [ t 1 2 rot my-mux ]
        [ t 1 2 ? ]
        same-type? ] unit-test

MACRO: my-if ( foo -- quot )
    drop [ if ] ;

{ t } [ [ 42 my-if ] [ if ] same-type? ] unit-test
{ t } [ [ [ 1 ] 42 my-if ] [ [ 1 ] if ] same-type? ] unit-test
{ t } [ [ [ 1 ] [ 2 ] 42 my-if ] [ [ 1 ] [ 2 ] if ] same-type? ] unit-test
{ t } [ [ [ 1 ] [ 1 ] 42 my-if ] [ [ 1 ] [ 1 ] if ] same-type? ] unit-test
{ t } [ [ [ [ if ] ] call [ 42 my-if ] call ] [ [ if ] if ] same-type? ]  unit-test
{ t } [ [ [ if ] 42 my-if ] [ [ if ] if ] same-type? ] unit-test

P{ Xor
  P{ Effect L{ ?x2 . ?i2 } L{ ?y2 . ?i2 } f { P{ Instance ?x2 object } P{ Neq ?x2 1 } P{ Instance ?y2 fixnum } P{ Eq ?y2 99 } } }
  P{ Effect L{ ?x1 . ?i1 } L{ ?y1 . ?i1 } f { P{ Instance ?x1 object } P{ Eq ?x1 1 } P{ Instance ?y1 fixnum } P{ Eq ?y1 42 } } }
}
[ [ { { [ dup 1 = ] [ drop 42 ] } [ drop 99 ] } cond ] get-type ] chr-test

! More than one arg
MACRO: my-foo ( x y -- quot )
    [ 4 + * ] 2curry ;

! TODO: nested expansions

! *** Iteration

: each-int-down ( ..a n quot: ( ..c i -- ..c ) -- ..b ) over 0 > [ [ 1 - ] dip [ call ] 2keep each-int-down ] [ 2drop ] if ; inline recursive

{ V{ 4 3 2 1 0 } }
[ V{ } clone 5 [ over push ] each-int-down ] unit-test


! FIXME: maybe do loop exit analysis better on this.  Right now, only works for step size 1...
: each-int-2down ( ..a n quot: ( ..c i -- ..c ) -- ..b ) over 0 > [ [ 2 - ] dip [ call ] 2keep each-int-2down ] [ 2drop ] if ; inline recursive

: each-down-int ( ..a n quot: ( ..c i -- ..c ) -- ..b ) [ call ] 2keep over 0 > [ [ 1 - ] dip each-down-int ] [ 2drop ] if ; inline recursive

: each-int-down-complete ( ..a n quot: ( i --  ) -- ..b  )
    over 0 < [ "negative accum" throw ] [ each-int-down ] if ; inline

[ V{ } clone -1 [ over push ] each-int-down-complete ] [ "negative accum" = ] must-fail-with

{ V{ 4 3 2 1 0 } }
[ V{ } clone 5 [ over push ] each-int-down-complete ] unit-test

! : if-zero

! stupid test word: increase n, decrease i, when done add 42 to n
! FIXME correctly infer stuff for given partial input!
! Approach: when rebuilding an effect containing a recursive call, and a known
! fixpoint type exists, then insert a fixpoint type iteration and a loop-step relation
: inc-int-down ( n i -- m )
    dup 0 > [ [ 1 + ] [ 1 - ] bi* inc-int-down ] [ drop 42 + ] if ;

{ 47 }
[ 1 4 inc-int-down ] unit-test


! ** Practical examples
P{
    Xor
    P{
        Effect
        L{ ?x1 ?y1 . ?a1 }
        L{ ?z1 . ?a1 }
        f
        { P{ Instance ?y1 number } P{ Instance ?x1 number } P{ Instance ?z1 t } P{ Eq ?z1 t } P{ Le ?x1 ?y1 } }
    }
    P{
        Effect
        L{ ?x2 ?y2 . ?a2 }
        L{ ?z2 . ?a2 }
        f
        { P{ Instance ?y2 number } P{ Instance ?x2 number } P{ Instance ?z2 POSTPONE: f } P{ Eq ?z2 f } P{ Lt ?y2 ?x2 } }
    }
}
[ [ >= ] get-type ] chr-test

! PREDICATE: u8 < integer { [ 0 >= ] [ 256 < ] } 1&& ;
PREDICATE: u8 < fixnum { [ 0 >= ] [ 256 < ] } 1&& ;

! Takes about 12 seconds right now
! [ u8? ] get-type
! (update) unfortunately, went up to 20 seconds with new liveness inference....

PREDICATE: cardinal < integer 0 > ;
PREDICATE: zero < integer 0 = ;

! [ dup 0 > [ [ 1 + ] [ 1 - ] bi* inc-int-down ] [ drop 42 + ] if ] ;

GENERIC: inc-loop ( n i -- m )
M: cardinal inc-loop [ 1 + ] [ 1 - ] bi* inc-loop ;
M: zero inc-loop drop 42 + ;

P{ Xor
   P{ Effect L{ ?x1 . ?a1 } L{ ?c1 . ?a1 } f { P{ Instance ?x1 integer } P{ Instance ?c1 t } P{ Eq ?c1 t } P{ Le 1 ?x1 } } }
   P{ Effect L{ ?x2 . ?a4 } L{ ?c2 . ?a4 } f { P{ Instance ?c2 POSTPONE: f } P{ Eq ?c2 f } P{ Instance ?x2 not{ cardinal } } } }
 }
[ [ cardinal? ] get-type ] chr-test

{ 47 } [ 0 5 inc-loop ] unit-test

{ t } [ cache-types? get ] unit-test

! TODO: shift must transport the Shift relation through the coercion
! in the bignum branch.  Unit-test this!

! TODO: must be nop: [ 1array dup 2 slot nip ]
! TODO: must infer [ 1array dup dup 2 set-slot ]
