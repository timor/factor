USING: accessors arrays assocs chr.factor.composition chr.parser chr.state
chr.test combinators.short-circuit kernel kernel.private lists literals math
math.private classes sequences.private
chr.factor.util layouts
quotations sequences slots.private terms tools.test typed types.util words
chr.factor chr.factor.word-types chr.factor.effects chr combinators ;

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
    P{ CompMode } suffix
    chr-comp swap [ run-chr-query store>> ] with-var-names
    values P{ CompMode } swap remove ;

: chr-simp1 ( constraints -- constraint )
    chr-simp first ;

: same-type? ( quot quot -- ? )
    [ get-type ] bi@ same-effect? ;

TYPED: array-first ( arr: array -- thing ) 2 slot ;

TERM-VARS: ?o ?a ?b ?v ?w ?x ?y ?z ;
TERM-VARS: ?y2 ?ys2 ?o4 ?a43 ?v6 ?y6 ?ys6 ;
TERM-VARS: ?y1 ?ys1 ?x1 ?v1 ?x2 ?x3 ?rho1 ?rho2 ?rho3 ?o1 ?a1 ;
TERM-VARS: ?i1 ?q1 ?q2 ?z1 ?i4 ?z6 ?i2 ?c1 ?a2 ?z2 ;


P{ Effect L{ ?o . ?a } L{ ?v . ?a } f {
       P{ Instance ?o array }
       P{ Instance ?v object }
       P{ Slot ?o 2 ?v } } }
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
{ t } [ [ 1 drop \ f ] [ 1 drop f ] same-type? ] unit-test

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
    ! subsumed
    ! P{ Effect L{ ?q3 ?p2 ?c2 . ?a4 } ?b3 f { P{ Instance ?q3 object } P{ Instance ?c2 not{ POSTPONE: f } } P{ Neq ?c f } P{ Instance ?p2 callable } P{ CallEffect ?p2 ?a4 ?b3 } } }
    P{ Effect L{ ?q3 ?p2 ?c2 . ?a4 } ?b3 f { P{ Instance ?q3 object } P{ Instance ?c2 not{ POSTPONE: f } } P{ Instance ?p2 callable } P{ CallEffect ?p2 ?a4 ?b3 } } }
    P{ Effect L{ ?q5 ?p3 ?c3 . ?a6 } ?b4 f { P{ Instance ?p3 object } P{ Instance ?c3 POSTPONE: f } P{ Eq ?c f } P{ Instance ?q5 callable } P{ CallEffect ?q5 ?a6 ?b4 } } }
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
                                        P{ Eq ?y ?x }
                                        P{ Le ?x $ most-positive-fixnum }
                                        P{ Le $ most-negative-fixnum ?x }
                                      } }
[ [ bignum>fixnum ] get-type ] chr-test

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


! ** Simple Dispatch
GENERIC: foothing ( obj -- result )
M: fixnum foothing 3 + ;
M: array foothing array-first ;

CONSTANT: foothing1
P{ Effect L{ ?y . ?a } L{ ?z . ?a } f { P{ Instance ?y fixnum } P{ Instance ?z integer } P{ Sum ?z ?y 3 } } }
foothing1
[ M\ fixnum foothing get-type ] chr-test

CONSTANT: foothing2
P{ Effect L{ ?o . ?a } L{ ?v . ?a } f { P{ Instance ?o array }
                                             P{ Instance ?v object } P{ Slot ?o 2 ?v } } }
foothing2
[ M\ array foothing get-type ] chr-test

P{ Xor $ foothing2 $ foothing1 }
[ \ foothing get-type ] chr-test

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
    P{ Effect L{ ?o4 . ?a43 } L{ ?v6 . ?a43 } f { P{ Instance ?o4 cons-state } P{ Slot ?o4 "cdr" ?v6 } P{ Instance ?v6 object } } }
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


{ t } [ \ auto-dispatch get-type \ manual-dispatch get-type isomorphic? ] unit-test


GENERIC: default-dispatch ( obj -- res )
M: list default-dispatch cdr>> ;
M: +nil+ default-dispatch ;

P{
    Xor
    P{ Effect L{ ?y1 . ?ys1 } L{ ?y1 . ?ys1 } f { P{ Instance ?y1 L{ } } P{ Eq ?y1 L{  } } } }
    P{ Effect L{ ?o1 . ?a1 } L{ ?v6 . ?a1 } f { P{ Instance ?o1 cons-state } P{ Slot ?o1 "cdr" ?v6 } P{ Instance ?v6 object } } }
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

! :)
{ t }
[ [ myloop ] [ loop ] same-type? ] unit-test

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

TERM-VARS: ?a15 ?o3 ?v3 ;

CONSTANT: sol1
P{
    Xor
    P{ Effect L{ ?y1 . ?ys1 } L{ ?y1 . ?ys1 } f { P{ Instance ?y1 L{ } } P{ Eq ?y1 L{  } } } }
    ! Finally able to infer the resolved recursion type...
    P{ Effect L{ ?x . ?a } L{ ?y . ?a } f { P{ Instance ?x cons-state } P{ Instance ?y L{  } } P{ Eq ?y L{  } } } }
    ! P{ Effect L{ ?o3 . ?a15 } ?b4 f { P{ CallRecursive __ ?a15 ?b4 } } }
}

sol1
[ [ lastcdr1 ] get-type ] chr-test

{ t }
[ [ lastcdr1 ] [ 1 drop lastcdr1 ] same-type? ] unit-test

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
[ [ [ lastcdr5 ] ] [ [ [ lastcdr5 ] ] (call) ] same-type? ] unit-test


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
    P{ Effect L{ ?y2 . ?ys2 } L{ ?y2 . ?ys2 } f { P{ Instance ?y2 not{ cons-state } } } }
    P{ Effect L{ ?x . ?a } L{ ?y . ?a } f { P{ Instance ?x cons-state } P{ Instance ?y not{ cons-state } } } }
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
    P{ Effect L{ ?y14 . ?ys14 } L{ ?y14 . ?ys14 } f { P{ Instance ?y14 intersection{ not{ cons-state } not{ array } } } } }
    P{
        Effect
        L{ ?o25 . ?a85 }
        L{ ?x17 . ?rho31 }
        f
        { P{ Instance ?x17 intersection{ not{ cons-state } not{ array } } } P{ Instance ?o25 union{ cons-state array } } }
    }
}
[ [ lastcdr7 ] get-type ] chr-test

! Same as lastcdr7, but as single word
: lastfoo ( x -- x )
    dup +nil+? [  ]
    [ dup list? [ cdr>> lastfoo ]
      [ dup array? [ array-first lastfoo ]
        [  ] if
      ] if
     ] if ;

! Stack checker examples
: bad ( ? quot: ( ? -- ) -- ) 2dup [ not ] dip bad call ; inline recursive
: good ( ? quot: ( ? -- ) -- ) [ good ] 2keep [ not ] dip call ; inline recursive

! ** Basic Mutual Recursion

DEFER: tok
: tik-tik ( x -- y ) 2 - tok ;
: tok ( x -- y ) 1 + dup 0 <= [ tik-tik ] unless ;

P{ Effect L{ ?x . ?a } L{ ?y . ?a } f { P{ Instance ?z number } P{ Instance ?y number } P{ Le ?y 0 } } }
[ [ tik-tik ] get-type ] chr-test

{ t } [ [ tik-tik ] [ 1 drop tik-tik ] same-type? ] unit-test
{ t } [ [ tik-tik ] [ tok ] same-type? ] unit-test

! ** Macro expansion
MACRO: my-add1 ( num -- quot )
    [ + ] curry ;

{ 42 } [ 41 1 my-add1 ] unit-test

P{ Effect L{ ?a1 . ?i1 } ?o1 { ?q1 } {
       P{ MacroExpand my-add1 f L{ ?a1 . ?i1 } ?q1 }
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
       P{ ExpandQuot [ [ + ] curry ] f L{ ?a1 . ?i1 } ?q1 1 }
       P{ Instance ?q1 callable }
       P{ CallEffect ?q1 ?i1 L{ ?a4 . ?i4 } }
       P{ ExpandQuot [ [ + 1 + ] curry ] f L{ ?a4 . ?i4 } ?q2 1 }
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


P{ Effect L{ ?a1 . ?i1 } ?o4 { ?a4 ?q1 } {
       P{ Instance ?a1 number }
       P{ ExpandQuot [ [ + 1 + ] curry ] f L{ ?a4 . ?i1 } ?q2 1 }
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
{ t } [ [ t 1 2 rot my-mux ] get-type
        [ t 1 2 ? ] get-type
        isomorphic? ] unit-test

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

PREDICATE: cardinal < integer 0 > ;
PREDICATE: zero < integer 0 = ;

! [ dup 0 > [ [ 1 + ] [ 1 - ] bi* inc-int-down ] [ drop 42 + ] if ] ;

GENERIC: inc-loop ( n i -- m )
M: cardinal inc-loop [ 1 + ] [ 1 - ] bi* inc-loop ;
M: zero inc-loop drop 42 + ;

P{ Xor
   P{ Effect L{ ?x1 . ?a1 } L{ ?c1 . ?a1 } f { P{ Instance ?x1 integer } P{ Instance ?c1 t } P{ Eq ?c1 t } P{ Lt 0 ?x1 } } }
   P{ Effect L{ ?x2 . ?a4 } L{ ?c2 . ?a4 } f { P{ Instance ?c2 POSTPONE: f } P{ Eq ?c2 f } P{ Instance ?x2 not{ cardinal } } } }
 }
[ [ cardinal? ] get-type ] chr-test

{ 47 } [ 0 5 inc-loop ] unit-test

! TODO: shift must transport the Shift relation through the coercion
! in the bignum branch.  Unit-test this!
