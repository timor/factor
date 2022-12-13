USING: accessors arrays assocs chr.factor.composition chr.parser chr.test
chr.state
combinators.short-circuit kernel kernel.private lists literals math quotations
sequences slots.private terms tools.test typed words ;
IN: chr.factor.composition.tests

! ** Test Helpers
: chr-simp ( constraints -- constraints )
    chr-comp swap [ run-chr-query store>> ] with-var-names
    values first ;

GENERIC: get-type ( quot -- type )

M: callable get-type
    [ qt values [ TypeOf? ] filter ]
    [ [ swap thing>> = ] curry find nip ] bi
    dup [ type>> ] when ;
M: word get-type
    1quotation get-type ;

TYPED: array-first ( arr: array -- thing ) 2 slot ;

TERM-VARS: ?o ?a ?b ?v ?x ?y ?z ;

P{ Effect L{ ?o . ?a } L{ ?v . ?a } { ?o } { P{ Instance ?o array } P{ Slot ?o W{ 2 } ?v } } }
[ \ array-first get-type ] chr-test

! ** Throwing
P{ Effect ?a ?b f { P{ Invalid } } }
[ [ "haha" throw ] get-type ] chr-test

! ** Normalization
P{ Neq ?a 42 }
[ { P{ Neq ?a 42 } } chr-simp ] chr-test

P{ Neq ?a 42 }
[ { P{ Neq 42 ?a } } chr-simp ] chr-test

P{ Eq ?a 42 }
[ { P{ Eq 42 ?a } } chr-simp1 ] chr-test

P{ Neq ?a ?b }
[ { P{ Neq ?a ?b } } chr-simp ] chr-test
P{ Neq ?b ?a }
[ { P{ Neq ?b ?a } } chr-simp ] chr-test
P{ Neq 42 43 }
[ { P{ Neq 42 43 } } chr-simp ] chr-test

! ** Basic Invariants

P{ Effect L{ ?a ?b . ?z } L{ ?a ?b . ?z } { } f }
[ [ swap swap ] get-type ] chr-test

P{ Effect L{ ?a ?b . ?z } L{ ?b ?a . ?z } { } f }
[ [ swap swap swap ] get-type ] chr-test

P{ Effect L{ ?x ?y . ?a } L{ ?z . ?a } { } { P{ Instance ?x number } P{ Instance ?y number } P{ Instance ?z number } P{ Sum ?z ?x ?y } } }
[ [ + ] get-type ] chr-test

TERM-VARS: ?q3 ?q5 ?p2 ?p3 ?c2 ?c3 ?a4 ?a6 ?b3 ?b4 ;
P{
    Xor
    P{ Effect L{ ?q3 ?p2 ?c2 . ?a4 } ?b3 { ?c2 } { P{ Instance ?c2 not{ W{ f } } } P{ Instance ?p2 callable } P{ CallEffect ?p2 ?a4 ?b3 } } }
    P{ Effect L{ ?q5 ?p3 ?c3 . ?a6 } ?b4 { ?c3 } { P{ Instance ?c3 W{ f } } P{ Instance ?q5 callable } P{ CallEffect ?q5 ?a6 ?b4 } } }
}
[ [ if ] get-type ] chr-test

P{ Effect ?a ?b f { P{ Invalid } } }
[ [ 42 2 slot ] get-type ] chr-test

{ f }
[ [ [ 42 2 slot ] [ "string" ] if ] get-type [ drop "string" ] get-type isomorphic? ] unit-test

{ t }
[ [ [ 42 2 slot ] [ "string" ] if ] get-type [ { W{ f } } declare drop "string" ] get-type isomorphic? ] unit-test

! ** Simple Dispatch
GENERIC: foothing ( obj -- result )
M: fixnum foothing 3 + ;
M: array foothing array-first ;

CONSTANT: foothing1
P{ Effect L{ ?y . ?a } L{ ?z . ?a } { ?y } { P{ Instance ?y fixnum } P{ Instance ?z number } P{ Sum ?z ?y 3 } } }
foothing1
[ M\ fixnum foothing get-type ] chr-test

CONSTANT: foothing2
P{ Effect L{ ?o . ?a } L{ ?v . ?a } { ?o } { P{ Instance ?o array } P{ Slot ?o W{ 2 } ?v } } }
foothing2
[ M\ array foothing get-type ] chr-test

P{ Xor $ foothing2 $ foothing1 }
[ \ foothing get-type ] chr-test

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

TERM-VARS: ?a15 ?y1 ?ys1 ?o3 ?v3 ;

CONSTANT: sol1
P{
    Xor
    P{ Effect L{ ?y1 . ?ys1 } L{ ?y1 . ?ys1 } { ?y1 } { P{ Instance ?y1 L{ } } } }
    P{ Effect L{ ?o3 . ?a15 } ?b4 { ?o3 } { P{ CallRecursive __ L{ ?v3 . ?a15 } ?b4 } P{ Instance ?o3 cons-state } P{ Slot ?o3 "cdr" ?v3 } P{ Instance ?v3 object } } }
}
! P{
!     Xor
!     P{ Effect ?a3 ?a3 f { P{ Declare L{ L{ } } ?a3 } } }
!     P{
!         Effect
!         L{ ?o3 . ?a11 }
!         ?b3 f
!         { P{ CallRecursive __ L{ ?v3 . ?a11 } ?b3 } P{ Instance ?o3 cons-state } P{ Slot ?o3 "cdr" ?v3 } }
!     }
! }

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

GENERIC: lastcdr5 ( list -- obj )
M: list lastcdr5 cdr>> lastcdr5 ;
M: +nil+ lastcdr5 ;
M: array lastcdr5 array-first lastcdr5 ;

{ t }
[ [ lastcdr5 ] get-type dup [ full-type? ] when ] unit-test

GENERIC: lastcdr4 ( list -- obj )
M: list lastcdr4 cdr>> [ [ lastcdr4 ] ] (call) (call) ;
M: +nil+ lastcdr4 ;
M: array lastcdr4 array-first lastcdr4 ;

{ t }
[ [ lastcdr4 ] get-type dup [ full-type? ] when ] unit-test

! NOTE: not working if we don't resolve the recursive call outputs eagerly
! { t }
! [ [ lastcdr4 dup drop ] get-type [ [ lastcdr4 ] (call) ] get-type isomorphic? ] unit-test

! NOTE: This one does not work because we don't recursively perform full phi-computations
! through multiple levels of nested effects
! { t }
{ f }
[ [ [ lastcdr5 ] ] get-type [ [ [ lastcdr5 ] ] (call) ] get-type isomorphic? ] unit-test


! Correct one
GENERIC: lastcdr6 ( list -- obj )
M: list lastcdr6 cdr>> lastcdr6 ;
M: +nil+ lastcdr6 ;
M: object lastcdr6 ;

{ +nil+ } [ L{ 12 } lastcdr6 ] unit-test
{ 42 } [ L{ 12 . 42 } lastcdr6 ] unit-test

! Stack checker examples
: bad ( ? quot: ( ? -- ) -- ) 2dup [ not ] dip bad call ; inline recursive
: good ( ? quot: ( ? -- ) -- ) [ good ] 2keep [ not ] dip call ; inline recursive

: each-int-down ( ..a n quot: ( i --  ) -- ..b ) over 0 > [ [ 1 - ] dip [ call ] 2keep each-int-down ] [ 2drop ] if ; inline recursive

{ V{ 4 3 2 1 0 } }
[ V{ } clone 5 [ over push ] each-int-down ] unit-test

: inc-int-down ( n i -- m )
    dup 0 > [ [ 1 + ] [ 1 - ] bi* inc-int-down ] [ drop 42 + ] if ;

! ** Practical examples

PREDICATE: u8 < integer { [ 0 >= ] [ 256 < ] } 1&& ;

PREDICATE: cardinal < integer 0 > ;
PREDICATE: zero < integer 0 = ;

GENERIC: inc-loop ( n i -- m )
M: cardinal inc-loop [ 1 + ] [ 1 - ] bi* inc-loop ;
M: zero inc-loop drop 42 + ;

! Note: taking this as an occasion to actually include the default method!

{ 47 } [ 0 5 inc-loop ] unit-test
