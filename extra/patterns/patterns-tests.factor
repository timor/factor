USING: match patterns.static patterns.terms tools.test ;
IN: patterns.tests

SYMBOL: Rec

MATCH-VARS: ?x ?f ;
CONSTANT: omega P{ Rec ?x -> ?x { Rec ?x } }
CONSTANT: fix P{ ?f -> omega { Rec P{ ?x -> ?f { omega ?x } } } }

{ { omega { Rec omega } } }
[ { omega { Rec omega } } spc-reduce ] unit-test

{ { omega { Rec P{ ?x -> ?f { omega ?x } } } } }
[ { fix ?f } spc-reduce ] unit-test
