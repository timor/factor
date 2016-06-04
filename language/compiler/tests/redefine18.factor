USING: kernel tools.test eval words ;
in: compiler.tests.redefine18

! Mixin bug found by Doug

GENERIC: g1 ( a -- b ) ;
GENERIC: g2 ( a -- b ) ;

mixin: c
singleton: a
INSTANCE: a c ;

M: c g1 g2 ;
M: a g2 drop a ;

mixin: d
INSTANCE: d c ;

M: d g2 drop d ;

[ ] [ "in: compiler.tests.redefine18 singleton: b INSTANCE: b d" eval( -- ) ] unit-test ;

[ d ] [ "b" "compiler.tests.redefine18" lookup-word g1 ] unit-test

[ ] [ "in: compiler.tests.redefine18 forget: b" eval( -- ) ] unit-test
