USING: literals math strings tools.test types.algebraic ;
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

${ 42 fixnum <literal> }
[ string <atomic> <not-type> 42 type-of intersect-types ] unit-test

{ +0+ }
[ number <atomic> <not-type> 42 type-of intersect-types ] unit-test

${ 42 type-of <not-type> }
[ 42 type-of <not-type> 42 type-of <not-type> intersect-types ] unit-test

${ T{ intersection-type f HS{ T{ not-type f T{ literal f "asf" string } } T{ atomic f fixnum } } } }
[ "asf" type-of <not-type> fixnum <atomic> intersect-types ] unit-test

${ T{ intersection-type f HS{ T{ not-type f T{ literal f "asf" string } } T{ not-type f T{ atomic f fixnum } } } } }
[ "asf" type-of <not-type> fixnum <atomic> <not-type> intersect-types ] unit-test
