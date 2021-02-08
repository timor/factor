USING: generic.multi kernel tools.test ;
IN: generic.multi.tests

TUPLE: A ;
MIXIN: B
TUPLE: C < A ;
MIXIN: D
TUPLE: E < C ;
INSTANCE: E B
INSTANCE: E D
TUPLE: F < C ;
INSTANCE: F D
TUPLE: G < E ;
TUPLE: H < F ;

CONSTANT: m1 { A B B B }
CONSTANT: m2 { C C B B }
CONSTANT: m3 { C D A F }

GENERIC: m ( x x x x -- n )
! Note, the primary dispatch classes are bogus here
M: A m ( x: A x: B x: B x: B -- n ) 4drop 1 ;
M: B m ( x: C x: C x: B x: B -- n ) 4drop 2 ;
M: C m ( x: C x: D x: A x: F -- n ) 4drop 3 ;

{ { A B B B } } [ M\ A m method-types ] unit-test
{ { C D A F } } [ M\ C m method-types ] unit-test

{ { C D E F } } [ { C D } subtype-closure ] unit-test
