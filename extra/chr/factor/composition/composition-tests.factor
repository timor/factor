USING: accessors arrays assocs chr.factor.composition chr.parser chr.state
chr.test combinators.short-circuit kernel kernel.private lists literals math
math.private classes
quotations sequences slots.private terms tools.test typed types.util words ;
IN: chr.factor.composition.tests

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
    chr-comp swap [ run-chr-query store>> ] with-var-names
    values ;

: chr-simp1 ( constraints -- constraint )
    chr-simp first ;

GENERIC: get-type ( quot -- type )

M: callable get-type
    [ qt values [ TypeOf? ] filter ]
    [ [ swap thing>> = ] curry find nip ] bi
    dup [ type>> ] when ;
M: word get-type
    1quotation get-type ;

TYPED: array-first ( arr: array -- thing ) 2 slot ;

TERM-VARS: ?o ?a ?b ?v ?w ?x ?y ?z ;

P{ Effect L{ ?o . ?a } L{ ?v . ?a } { ?o } {
       P{ Instance ?o array }
       P{ Instance ?v object }
       P{ Slot ?o W{ 2 } ?v } } }
[ \ array-first get-type ] chr-test

! ** Throwing
P{ Effect ?a ?b f { P{ Invalid } } }
[ [ "haha" throw ] get-type ] chr-test

TERM-VARS: ?c ?d ;
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
P{ Neq 42 43 }
[ { P{ Neq 42 43 } } chr-simp1 ] chr-test

{ { P{ Instance ?a number } } }
[ { P{ Neq ?a "haha" } P{ Instance ?a number } } chr-simp ] unit-test

! ** Basic Invariants
{ t }
[ [ if* ] get-type valid-effect-type? ] unit-test

P{ Effect L{ ?a ?b . ?z } L{ ?a ?b . ?z } f { P{ Instance ?a object }
                                                P{ Instance ?b object } } }
[ [ swap swap ] get-type ] chr-test

P{ Effect L{ ?a ?b . ?z } L{ ?b ?a . ?z } f { P{ Instance ?a object }
                                                P{ Instance ?b object } } }
[ [ swap swap swap ] get-type ] chr-test

P{ Effect L{ ?x ?y . ?a } L{ ?z . ?a } f { P{ Instance ?x number } P{ Instance ?y number } P{ Instance ?z number } P{ Sum ?z ?x ?y } } }
[ [ + ] get-type ] chr-test

{ t }
[ [ [ ? ] ] get-type [ [ [ ? ] ] (call) ] get-type isomorphic? ] unit-test

{ t }
[ [ [ if ] ] get-type [ [ [ if ] ] (call) ] get-type isomorphic? ] unit-test

{ t }
[ [ [ [ if ] ] ] get-type [ [ [ [ if ] ] ] (call) ] get-type isomorphic? ] unit-test

TERM-VARS: ?q3 ?q5 ?p2 ?p3 ?c2 ?c3 ?a4 ?a6 ?b3 ?b4 ;
! NOTE: This is interesting: because we have [ ? ] as basis, we don't enforce
! that the non-taken branch quotation is actually a quotation!
P{
    Xor
    P{ Effect L{ ?q3 ?p2 ?c2 . ?a4 } ?b3 { ?c2 } { P{ Instance ?q3 object } P{ Instance ?c2 not{ POSTPONE: f } } P{ Instance ?p2 callable } P{ CallEffect ?p2 ?a4 ?b3 } } }
    P{ Effect L{ ?q5 ?p3 ?c3 . ?a6 } ?b4 { ?c3 } { P{ Instance ?p3 object } P{ Instance ?c3 POSTPONE: f } P{ Instance ?q5 callable } P{ CallEffect ?q5 ?a6 ?b4 } } }
}
[ [ if ] get-type ] chr-test

P{ Effect ?a ?b f { P{ Invalid } } }
[ [ 42 2 slot ] get-type ] chr-test

P{ Effect ?a ?b f { P{ Invalid } } }
[ [ curry (call) ] get-type ] chr-test

! NOTE: This would only work if we decide to implement normal forms for the nominative type segment?
{ f }
[ [ compose call ] get-type [ [ call ] dip call ] get-type isomorphic? ] unit-test

{ f }
[ [ [ 42 2 slot ] [ "string" ] if ] get-type [ drop "string" ] get-type isomorphic? ] unit-test

{ t }
[ [ [ 42 2 slot ] [ "string" ] if ] get-type [ { POSTPONE: f } declare drop "string" ] get-type isomorphic? ] unit-test

P{ Effect L{ ?y . ?a } L{ ?x . ?a } { ?y }
   { P{ Instance ?y object } P{ Instance ?x W{ 4 } } } }
[ [ number? 4 4 ? ] get-type ] chr-test

{ t }
[ [ number? 4 5 ? ] get-type Xor? ] unit-test

! FIXME
{ t }
[ [ callable? ] get-type [ callable instance? ] get-type isomorphic? ] unit-test

{ t }
[ [ + 5 = [ swap ] when ] get-type Xor? ] unit-test

P{ Effect L{ ?x . ?a } L{ ?y . ?a } f { P{ Instance ?x bignum } P{ Instance ?y fixnum } } }
[ [ bignum>fixnum ] get-type ] chr-test

! ** Simple Dispatch
GENERIC: foothing ( obj -- result )
M: fixnum foothing 3 + ;
M: array foothing array-first ;

CONSTANT: foothing1
P{ Effect L{ ?y . ?a } L{ ?z . ?a } { ?y } { P{ Instance ?y fixnum } P{ Instance ?z number } P{ Sum ?z ?y 3 } } }
foothing1
[ M\ fixnum foothing get-type ] chr-test

CONSTANT: foothing2
P{ Effect L{ ?o . ?a } L{ ?v . ?a } { ?o } { P{ Instance ?o array }
                                             P{ Instance ?v object } P{ Slot ?o W{ 2 } ?v } } }
foothing2
[ M\ array foothing get-type ] chr-test

P{ Xor $ foothing2 $ foothing1 }
[ \ foothing get-type ] chr-test

! ** Overlapping dispatch
GENERIC: auto-dispatch ( obj -- res )
M: list auto-dispatch cdr>> ;
M: +nil+ auto-dispatch ;
M: object auto-dispatch ;

{ { L{ } cons-state intersection{ not{ cons-state } not{ L{ } } } } }
[ \ auto-dispatch dispatch-method-seq keys ] unit-test

TERM-VARS: ?y2 ?ys2 ?o4 ?a43 ?v6 ?y6 ?ys6 ;
P{
    Xor
    P{ Effect L{ ?y2 . ?ys2 } L{ ?y2 . ?ys2 } { ?y2 } { P{ Instance ?y2 not{ cons-state } } } }
    P{ Effect L{ ?o4 . ?a43 } L{ ?v6 . ?a43 } { ?o4 } { P{ Instance ?o4 cons-state } P{ Slot ?o4 "cdr" ?v6 } P{ Instance ?v6 object } } }
}
[ \ auto-dispatch get-type ] chr-test

! TODO: investigate why manual-dispatch takes ages compared to auto-dispatch
: manual-dispatch ( obj -- res )
    dup +nil+? [  ]
    [ dup list? [ cdr>> ] [  ] if ] if ;

{ 42 } [ 42 manual-dispatch ] unit-test
{ L{ 42 } } [ L{ 43 42 } manual-dispatch ] unit-test
{ +nil+ } [ L{ } manual-dispatch ] unit-test

TERM-VARS: ?y1 ?ys1 ?x1 ?v1 ?x2 ?x3 ?rho1 ?rho2 ?rho3 ?o1 ?a1 ;
P{
    Xor
    P{ Effect L{ ?x1 . ?rho1 } L{ ?x1 . ?rho1 } { ?x1 } { P{ Instance ?x1 not{ cons-state } } } }
    P{
        Effect
        L{ ?x2 . ?rho2 }
        L{ ?v1 . ?rho2 }
        { ?x2 }
        { P{ Instance ?x2 cons-state } P{ Slot ?x2 "cdr" ?v1 } P{ Instance ?v1 object } }
    }
}
[ \ manual-dispatch get-type ] chr-test


{ t } [ \ auto-dispatch get-type \ manual-dispatch get-type isomorphic? ] unit-test


GENERIC: default-dispatch ( obj -- res )
M: list default-dispatch cdr>> ;
M: +nil+ default-dispatch ;

P{
    Xor
    P{ Effect L{ ?y1 . ?ys1 } L{ ?y1 . ?ys1 } { ?y1 } { P{ Instance ?y1 L{ } } } }
    P{ Effect L{ ?o1 . ?a1 } L{ ?v6 . ?a1 } { ?o1 } { P{ Instance ?o1 cons-state } P{ Slot ?o1 "cdr" ?v6 } P{ Instance ?v6 object } } }
}
[ \ default-dispatch get-type ] chr-test

! ** Mutually recursive definitions

! : nop ( -- ) ;
GENERIC: mylastcdr ( list -- obj )
M: list mylastcdr

    ! RES3 needed for [ mylastcdr ]
    ! not working with [ [ mylastcdr ] ] (neither RES1,2,3 cause progress)
    ! RES2 needed for [ [ mylastcdr ] (call) ]
    ! cdr>> [ mylastcdr ] (call) ;

    ! HA! This works with RES2!
    ! cdr>> [ nop mylastcdr ] (call) ;

    ! nop cdr>> [ mylastcdr ] (call) ;

    ! cdr>> nop [ mylastcdr ] (call) ;


    cdr>> [ [ mylastcdr ] ] (call) (call) ; ! Doesnt work so well...

    ! RES3 needed for [ mylastcdr ]
    ! RES1 needed for [ [ mylastcdr ] ]
    ! RES3 needed for [ [ mylastcdr ] (call) ]
    ! RES2 needed for [ [ [ mylastcdr ] (call) ] (call) ]
    ! RES1 needed for [ [ [ mylastcdr ] ] (call) (call) ]
    ! cdr>> [ [ mylastcdr ] (call) ] (call) ; ! Works well

    ! seems to work with all combinations...
    ! cdr>> mylastcdr ;

M: +nil+ mylastcdr ;
! M: object mylastcdr ;
! M: array mylastcdr 2 slot [ mylastcdr ] (call) ;
! M: array mylastcdr array-first mylastcdr ;
M: array mylastcdr array-first [ [ mylastcdr ] ] (call) (call) ;
! M: array mylastcdr array-first [ [ mylastcdr ] (call) ] (call) ;

! Needs make-unit recursion resolution in some form...
: myloop ( -- ) [ call ] keep swap [ myloop ] [ drop ] if ; inline recursive

{ t } [ [ myloop ] get-type dup [ full-type? ] when ] unit-test

GENERIC: lastcdr1 ( list -- obj )
M: list lastcdr1 cdr>> lastcdr1 ;
M: +nil+ lastcdr1 ;

TERM-VARS: ?a15 ?o3 ?v3 ;

CONSTANT: sol1
P{
    Xor
    P{ Effect L{ ?y1 . ?ys1 } L{ ?y1 . ?ys1 } { ?y1 } { P{ Instance ?y1 L{ } } } }
    P{ Effect L{ ?o3 . ?a15 } ?b4 { ?o3 } { P{ CallRecursive __ L{ ?v3 . ?a15 } ?b4 } P{ Instance ?o3 cons-state } P{ Slot ?o3 "cdr" ?v3 } P{ Instance ?v3 object } } }
}

sol1
[ [ lastcdr1 ] get-type ] chr-test

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

GENERIC: lastcdr4 ( list -- obj )
M: list lastcdr4 cdr>> [ [ lastcdr4 ] ] (call) (call) ;
M: +nil+ lastcdr4 ;
M: array lastcdr4 array-first lastcdr4 ;

{ t }
[ [ lastcdr4 ] get-type dup [ full-type? ] when ] unit-test

! NOTE: not working if we don't resolve the recursive call outputs eagerly
! { t }
! [ [ lastcdr4 dup drop ] get-type [ [ lastcdr4 ] (call) ] get-type isomorphic? ] unit-test

GENERIC: lastcdr5 ( list -- obj )
M: list lastcdr5 cdr>> lastcdr5 ;
M: +nil+ lastcdr5 ;
M: array lastcdr5 array-first lastcdr5 ;

{ t }
[ [ lastcdr5 ] get-type dup [ full-type? ] when ] unit-test


! (old)NOTE: This one does not work because we don't recursively perform full phi-computations
! through multiple levels of nested effects (yet?)
! (update) Fixed by not phi-merging anything to do with unresolved computations
{ t }
[ [ [ lastcdr5 ] ] get-type [ [ [ lastcdr5 ] ] (call) ] get-type isomorphic? ] unit-test


! Correct one
GENERIC: lastcdr6 ( list -- obj )
M: list lastcdr6 cdr>> lastcdr6 ;
M: +nil+ lastcdr6 ;
M: object lastcdr6 ;

{ +nil+ } [ L{ 12 } lastcdr6 ] unit-test
{ 42 } [ L{ 12 . 42 } lastcdr6 ] unit-test

TERM-VARS: ?o5 ?a47 ?b34 ?v7 ;
P{
    Xor
    P{ Effect L{ ?y2 . ?ys2 } L{ ?y2 . ?ys2 } { ?y2 } { P{ Instance ?y2 not{ cons-state } } } }
    P{
        Effect
        L{ ?o5 . ?a47 }
        ?b34
        { ?o5 }
        { P{ CallRecursive lastcdr6 L{ ?v7 . ?a47 } ?b34 } P{ Instance ?o5 cons-state } P{ Slot ?o5 "cdr" ?v7 } P{ Instance ?v7 object } }
    }
}
[ [ lastcdr6 ] get-type ] chr-test

! With array exception
GENERIC: lastcdr7 ( list -- obj )
M: list lastcdr7 cdr>> lastcdr7 ;
M: array lastcdr7 array-first lastcdr7 ;
M: +nil+ lastcdr7 ;
M: object lastcdr7 ;

TERM-VARS: ?y14 ?ys14 ?o25 ?a85 ?x17 ?rho31 ;
P{
    Xor
    P{ Effect L{ ?y14 . ?ys14 } L{ ?y14 . ?ys14 } { ?y14 } { P{ Instance ?y14 intersection{ not{ cons-state } not{ array } } } } }
    P{
        Effect
        L{ ?o25 . ?a85 }
        L{ ?x17 . ?rho31 }
        { ?o25 }
        { P{ Instance ?o25 union{ cons-state array } } P{ Instance ?x17 intersection{ not{ cons-state } not{ array } } } }
    }
}
[ [ lastcdr7 dup drop ] get-type ] chr-test

! Stack checker examples
: bad ( ? quot: ( ? -- ) -- ) 2dup [ not ] dip bad call ; inline recursive
: good ( ? quot: ( ? -- ) -- ) [ good ] 2keep [ not ] dip call ; inline recursive

: each-int-down ( ..a n quot: ( i --  ) -- ..b ) over 0 > [ [ 1 - ] dip [ call ] 2keep each-int-down ] [ 2drop ] if ; inline recursive

{ V{ 4 3 2 1 0 } }
[ V{ } clone 5 [ over push ] each-int-down ] unit-test

: each-int-down-complete ( ..a n quot: ( i --  ) -- ..b  )
    over 0 < [ "negative accum" throw ] [ each-int-down ] if ; inline

[ V{ } clone -1 [ over push ] each-int-down-complete ] [ "negative accum" = ] must-fail-with

{ V{ 4 3 2 1 0 } }
[ V{ } clone 5 [ over push ] each-int-down-complete ] unit-test

! stupid test word: increase n, decrease i, when done add 42 to n
: inc-int-down ( n i -- m )
    dup 0 > [ [ 1 + ] [ 1 - ] bi* inc-int-down ] [ drop 42 + ] if ;

{ 47 }
[ 1 4 inc-int-down ] unit-test

! ** Practical examples

PREDICATE: u8 < integer { [ 0 >= ] [ 256 < ] } 1&& ;

PREDICATE: cardinal < integer 0 > ;
PREDICATE: zero < integer 0 = ;

GENERIC: inc-loop ( n i -- m )
M: cardinal inc-loop [ 1 + ] [ 1 - ] bi* inc-loop ;
M: zero inc-loop drop 42 + ;

! Note: taking this as an occasion to actually include the default method!

{ 47 } [ 0 5 inc-loop ] unit-test
