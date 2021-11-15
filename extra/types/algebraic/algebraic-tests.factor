USING: literals math tools.test types.algebraic ;
IN: types.algebraic.tests

${ 1 fixnum <literal> }
[ 1 type-of ] unit-test

${ 42 fixnum <literal> }
[ integer <atomic> 42 type-of intersect-types ] unit-test

{ +1+ }
[ +1+ +1+ intersect-types ] unit-test

{ +0+ }
[ +0+ +1+ intersect-types ] unit-test

{ +0+ }
[ integer <atomic> string <atomic> intersect-types ] unit-test
