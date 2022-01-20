USING: match patterns.static patterns.terms tools.test ;
IN: patterns.tests

SYMBOL: Rec

MATCH-VARS: ?x ?y ?z ?f ?r ?s ?t ;
CONSTANT: omega P{ Rec ?x -> ?x { Rec ?x } }
CONSTANT: fix P{ ?f -> omega { Rec P{ ?x -> ?f { omega ?x } } } }

{ { omega { Rec omega } } }
[ { omega { Rec omega } } spc-reduce ] unit-test

{ { omega { Rec P{ ?x -> ?f { omega ?x } } } } }
[ { fix ?f } spc-reduce ] unit-test

SYMBOLS: Nil Cons ;
DEFER: _append
CONSTANT: _append Ext{ Nil -> P{ ?z -> ?z } | P{ Cons ?x ?y -> P{ ?z -> Cons ?x { _append ?y ?z } } } }

{ { Cons ?r { Cons ?s { Cons ?t Nil } } } }
[ { _append { Cons ?r Nil } { Cons ?s { Cons ?t Nil } } } spc-reduce ] unit-test

! Does this work without fixpoints?
DEFER: mapList
CONSTANT: mapList P{ ?f -> Ext{ Nil -> Nil | P{ Cons ?x ?y -> Cons { ?f ?x } { mapList ?f ?y } } } }

SYMBOL: foo
! Seems to!  Don't know if this is because of the naive fixpoint check though...
{ { Cons { foo ?s } { Cons { foo ?t } Nil } } }
[ { mapList foo { Cons ?s { Cons ?t Nil } } } spc-reduce ] unit-test
