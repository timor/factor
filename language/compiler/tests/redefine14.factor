USING: compiler.units definitions tools.test sequences ;
in: compiler.tests.redefine14

TUPLE: bad ;

M: bad length 1 2 3 ;

[ ] [ [ M\ bad length forget ] with-compilation-unit ] unit-test
