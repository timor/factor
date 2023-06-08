USING: accessors arrays assocs chr.factor chr.factor.composition
chr.factor.effects chr.factor.phi chr.factor.util chr.parser chr.state chr.test
classes combinators combinators.short-circuit grouping kernel kernel.private
layouts lists literals locals.backend math math.private namespaces quotations
sequences slots.private strings terms tools.test typed types.util words ;

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

TERM-VARS: ?o ?a ?b ?v ?w ?x ?y ?z ;
TERM-VARS: ?y2 ?ys2 ?o4 ?a43 ?y6 ?ys6 ;
TERM-VARS: ?y1 ?ys1 ?x1 ?v1 ?x2 ?x3 ?rho1 ?rho2 ?rho3 ?o1 ?a1 ;
TERM-VARS: ?i1 ?q1 ?q2 ?z1 ?i4 ?z6 ?i2 ?c1 ?a2 ?z2 ;
TERM-VARS: ?c ?d ;
TERM-VARS: ?q3 ?q5 ?p2 ?p3 ?c2 ?c3 ?a4 ?a6 ?b3 ?b4 ;
TERM-VARS: ?a15 ?o3 ?v3 ;
TERM-VARS: ?o5 ?a47 ?b34 ?v7 ;
TERM-VARS: ?y14 ?ys14 ?o25 ?a85 ?x17 ?rho31 ;

P{ Effect L{ ?o3 . ?a6 } L{ ?v3 . ?c3 } { ?x1 ?b4 ?x2 }
    {
        P{ Instance ?o3 array }
        P{ Instance ?v3 object }
        P{ Eq ?x2 2 }
        P{ Instance ?x2 fixnum }
        P{ SlotLoc ?x1 ?o3 ?x2 }
        P{ PushLoc ?x1 ?b4 L{ ?v3 } ?c3 f }
        P{ LocPop ?x1 ?a6 L{ ?v3 } ?b4 f ?a6 } } }
[ \ array-first get-type ] chr-test

{ t } [ [ 1 drop 42 ] [ { 42 } array-first ] same-type? ] unit-test
{ t } [ [ 1 drop 42 ] [ { 42 43 } array-first ] same-type? ] unit-test

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

{ { P{ Invalid } } } [ { P{ Neq 5 5 } } chr-simp ] unit-test
{ { P{ Invalid } } } [ { P{ Neq f f } } chr-simp ] unit-test
{ { P{ Invalid } } } [ { P{ Neq ?c ?c } } chr-simp ] unit-test
{ { P{ Neq ?c ?d } } } [ { P{ Neq ?c ?d } } chr-simp ] unit-test
{ { P{ Neq ?c 5 } } } [ { P{ Neq ?c 5 } } chr-simp ] unit-test
{ { } } [ { P{ Neq f t } } chr-simp ] unit-test

{ t } [ [ drop t ] [ dup eq? ] same-type? ] unit-test

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

{ t } [ [ swap swap swap ] [ [ swap ] curry curry call ] same-type? ] unit-test
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

! NOTE: those stupid drops are in there because otherwise we just
! get the wrapper type... meh
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

P{ Xor
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

! ** Effectful access
! Effect must survive
P{
    Effect
    L{ ?o1 ?v1 . ?a1 }
    ?c2
    { ?x2 ?z2 ?b3 ?x3 }
    {
        P{ Instance ?o1 not{ fixnum } }
        P{ Instance ?v1 object }
        P{ Eq ?x3 2 }
        P{ Instance ?x3 fixnum }
        P{ SlotLoc ?x2 ?o1 ?x3 }
        P{ PushLoc ?x2 ?b3 L{ ?v1 } ?c2 f }
        P{ LocPop ?x2 ?a1 L{ ?z2 } ?b3 f ?a1 }
    }
} [ [ 2 set-slot ] get-type ] chr-test

! Local allocations, writeback should be ignored
P{ Effect ?a1 ?a1 f f }
[ [ 42 { 43 } 2 set-slot ] get-type ] chr-test

P{ Effect L{ ?z . ?a } ?a f { P{ Instance ?z object } } }
[ [ 1array 42 swap 2 set-slot ] get-type ] chr-test

! Flushable, thus can be ignored
! NOTE: not doing that.  Only done on local allocations!
P{
    Effect L{ ?o3 . ?a } ?c3 { ?x1 ?v3 ?b ?x2 }
    {
        P{ Instance ?o3 not{ fixnum } }
        P{ Eq ?x2 2 }
        P{ Instance ?x2 fixnum }
        P{ SlotLoc ?x1 ?o3 ?x2 }
        P{ PushLoc ?x1 ?b L{ ?v3 } ?c3 f }
        P{ Instance ?v3 object }
        P{ LocPop ?x1 ?a L{ ?v3 } ?b f ?a } } }
[ [ 2 slot drop ] get-type ] chr-test

P{ Effect L{ ?v . ?a } ?a f { P{ Instance ?v object } } }
[ [ 1array 2 slot drop ] get-type ] chr-test

! *** basic array manipulation

P{
    Effect
    ?a1
    L{ ?v1 ?x1 . ?a1 }
    f
    { P{ Instance ?x1 array } P{ Instance ?v1 fixnum } P{ Eq ?v1 42 } P{ Eq ?x1 { 42 } }
      P{ LocalAllocation ?a1 ?x1 } } }
[ [ { 43 } 42 over 2 set-slot dup 2 slot ] get-type ] chr-test

! *** Some cloning class predicate stuff
P{ Effect ?a ?b f { P{ Invalid } } }
[ [ { array } declare (clone) { string } declare ] get-type ] chr-test

! TODO: tests for actually specializing stuff over clone...

TUPLE: footuple barslot ;
P{
    Effect
    L{ ?o . ?a }
    L{ ?v . ?b }
    { ?x1 ?y1 ?z1 }
    {
        P{ Instance ?v object }
        P{ Instance ?o footuple }
        P{ Eq ?z1 2 }
        P{ Instance ?z1 fixnum }
        P{ SlotLoc ?x1 ?o ?z1 }
        P{ PushLoc ?x1 ?y1 L{ ?v } ?b f }
        P{ LocPop ?x1 ?a L{ ?v } ?y1 f ?a }
    }
}
[ [ barslot>> ] get-type ] chr-test

TUPLE: foo2 aslot { bslot read-only } ;

P{ Effect L{ ?o . ?a } L{ ?v . ?a } f { P{ Slot ?o "bslot" ?v } P{ Instance ?v object } P{ Instance ?o foo2 } } }
[ [ bslot>> ] get-type ] chr-test

P{ Effect L{ ?x . ?a } L{ ?z . ?a } { ?y } {
       P{ Instance ?y foo2 }
       P{ Instance ?x foo2 }
       P{ Slot ?x "bslot" ?y }
       P{ Slot ?y "bslot" ?z }
       P{ Instance ?z object }
   }
 } [ [ bslot>> bslot>> ] get-type ] chr-test


! *** Infinite Structures

! Setting an array's first element to itself, dereferencing
! That's a pretty interesting case, because it actually results in a hybrid literal structure
! being created, as in P{ Eq ?x11 { ?x11 } }, which is neither a factor literal, not a type variable.
! Looks cool because it seems we get recursive structure prototypes for free?
! This one only works as long as no specialized slots are involved
{ t } [ [ { 42 } dup dup 2 set-slot 2 slot ]
        [ { 42 } dup dup 2 set-slot 2 slot 2 slot ]
        same-type? ] unit-test

! This one should work for all kind of data, as it describes the structure (construction)
! rather than building the literal
{ t } [ [ 1array dup dup 2 set-slot 2 slot ]
        [ 1array dup dup 2 set-slot 2 slot 2 slot ]
        same-type? ] unit-test

! ** Sums and Parameters
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
{ 3 } [ [ - 2 swap - swap + ] get-type preds>> [ Sum? ] count ] unit-test

{ 1 } [ [ [ + ] [ swap + ] if ] get-type preds>> [ Sum? ] count ] unit-test

! ** Read-only locals

{ 1 } [ [ + load-local ] get-type preds>> [ Sum? ] count ] unit-test
{ 1 } [ [ 0 get-local + ] get-type preds>> [ Sum? ] count ] unit-test
{ 1 } [ [ 0 get-local -1 get-local + ] get-type preds>> [ Sum? ] count ] unit-test

! FIXME: fail due to missing implicit declarations
{ t } [ [ swap ] [| a b | b a ] same-type? ] unit-test
{ t } [ [ swap ] [| | :> a :> b a b ] same-type? ] unit-test
{ t } [ [ swap swap drop ] [| | :> a :> b a ] same-type? ] unit-test
{ t } [ [ swap swap drop ] [| a b | a ] same-type? ] unit-test
{ t } [ [ nip ] [| a b | a ] same-type? ] unit-test
{ t } [ [ + ] [| a b | a b + :> c c ] same-type? ] unit-test
{ t } [ [ + dup ] [ [ [| | :> a a + ] [ dup ] compose ] call call ] same-type? ] unit-test

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
[ [| a! | a a ] get-type ] chr-test

P{ Effect L{ ?x . ?a } L{ ?x ?x ?x . ?a } f { P{ Instance ?x object } } }
[ [| a! | a a a ] get-type ] chr-test

P{ Effect L{ ?x . ?a } L{ ?x ?x ?x ?x . ?a } f { P{ Instance ?x object } } }
[ [| a! | a a a a ] get-type ] chr-test

P{ Effect L{ ?x . ?a } L{ ?x ?x ?x ?x ?x . ?a } f { P{ Instance ?x object } } }
[ [| a! | a a a a a ] get-type ] chr-test

! FIXME
[| | :> a a 2 slot a 2 slot a 2 slot a 2 slot ]

! ** Nested local allocations
{ t } [ [ 1array ] [ 1array 1array 2 slot ] same-type? ] unit-test

P{ Effect L{ ?v . ?a } L{ ?v . ?a } f { P{ Instance ?v object } } }
[ [ 1array 1array 2 slot 2 slot ] get-type ] chr-test

P{ Effect L{ ?v . ?a } ?a  f { P{ Instance ?v object } } }
[ [ 1array 1array 2 slot 2 slot drop ] get-type ] chr-test

! ** TODO Effectful Predicates Phi

! ** Simple Dispatch
GENERIC: foothing ( obj -- result )
M: fixnum foothing 3 + ;
M: array foothing array-first ;

! FIXME
CONSTANT: foothing1
P{ Effect L{ ?y . ?b } L{ ?z . ?b } f { P{ Instance ?y fixnum } P{ Instance ?z integer } P{ Sum ?z ?y 3 } } }

! Note: extra stuff because need to expand to the call type
foothing1
[ M\ fixnum foothing 1quotation [ call ] curry get-type ] chr-test

! FIXME
CONSTANT: foothing2
P{
    Effect L{ ?o . ?a } L{ ?v . ?c } { ?x ?b } {
        P{ Instance ?o array }
        P{ Instance ?v object }
        P{ SlotLoc ?x ?o 2 }
        P{ PushLoc ?x ?b L{ ?v } ?c f }
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
