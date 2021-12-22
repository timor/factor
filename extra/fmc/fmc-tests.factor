USING: tools.test fmc ;
IN: fmc.tests

: add ( a b -- c ) fixnum+ ;

: rec ( x -- x ) rec ;

[ [ rec ] >fmc ] must-fail

{  }
[ [ [ swap add ] >fmc pprint-fmc ] with-var-names ] unit-test
