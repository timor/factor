USING: continuations kernel lists match math patterns.reduction patterns.terms
quotations tools.test words ;
IN: patterns.tests

USE: patterns.static

SYMBOL: Rec

MATCH-VARS: ?x ?y ?z ?f ?r ?s ?t ;
CONSTANT: omega P{ Rec ?x -> ?x { Rec ?x } }
CONSTANT: fix P{ ?f -> omega { Rec P{ ?x -> ?f { omega ?x } } } }

{ { omega { Rec omega } } }
[ { omega { Rec omega } } pc-reduce ] unit-test

{ { omega { Rec P{ ?x -> ?f { omega ?x } } } } }
[ { fix ?f } pc-reduce ] unit-test

SYMBOLS: Nil Cons ;
DEFER: _append
CONSTANT: _append Ext{ Nil -> P{ ?z -> ?z } | P{ Cons ?x ?y -> P{ ?z -> Cons ?x { _append ?y ?z } } } }

{ { Cons ?r { Cons ?s { Cons ?t Nil } } } }
[ { _append { Cons ?r Nil } { Cons ?s { Cons ?t Nil } } } pc-reduce ] unit-test

! Does this work without fixpoints?
DEFER: mapList
CONSTANT: mapList P{ ?f -> Ext{ Nil -> Nil | P{ Cons ?x ?y -> Cons { ?f ?x } { mapList ?f ?y } } } }

SYMBOL: foo
! Seems to!  Don't know if this is because of the naive fixpoint check though...
{ { Cons { foo ?s } { Cons { foo ?t } Nil } } }
[ { mapList foo { Cons ?s { Cons ?t Nil } } } pc-reduce ] unit-test

SYMBOLS: Leaf Node ;
DEFER: mapTree
CONSTANT: mapTree P{ ?f ->
                     Ext{ Leaf ?x -> Leaf { ?f ?x } |
                          P{ Node ?x ?y -> Node { mapTree ?f ?x } { mapTree ?f ?y }
                           } } }

{ { Node { Leaf { foo 5 } } { Leaf { foo 6 } } } }
[ { mapTree foo { Node { Leaf 5 } { Leaf 6 } } } pc-reduce ] unit-test

! Some Stack experiments

! : >stack ( seq -- term )
!     [ Push swap 2array ] map concat ;
! GENERIC: >term ( obj -- term )
! M: object >term { Push }
SYMBOLS: Val Quot Stack Push ;
! \ swap P< [ x y ] { Val M< x > } { Val < y > } -> { Val y } { Val x } | > "pattern" set-word-prop
! \ drop P< [ x ] Val M< x > -> | > "pattern" set-word-prop
! \ dup P< [ x ] Val M< x > -> { Val x } { Val x } | > "pattern" set-word-prop

! Eval Push -> x
! Eval Word x -> Eval Word Push { Eval x }
! Eval { 1 2 dup } ->


! Eval Push x -> x
! Eval Word x y -> Eval
M: callable pc-reduce-step
    [ call( -- term ) t ] [ drop f ] recover ;

CONSTANT: Plus lam{ x lam{ y [ x y + ] } }

\ swap P< [ x y r ] L{ M< x > M< y > . M< r > } -> L{ y x . r } | > "pattern" set-word-prop
\ drop P< [ x r ] L{ M< x > . M< r > } -> r | > "pattern" set-word-prop
\ dup P< [ x r ]  L{ M< x > . M< r > } -> L{ x x . r } | > "pattern" set-word-prop
