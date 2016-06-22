USING: eval tools.test ;
IN: eval.tests

{ 4 } [ "use: math 2 2 +" eval( -- result ) ] unit-test
[ "use: math 2 2 +" eval( -- ) ] must-fail
{ "4\n" } [ "USING: math prettyprint ; 2 2 + ." eval>string ] unit-test
