USING: alien.c-types math tools.test types.typestack ;
IN: types.typestack.tests

{ { 1 } { 2 3 } }
[ { 1 2 3 } 2 pop-types ] unit-test

{ { } { 1 2 3 } }
[ { 1 2 3 } { integer fixnum bool } ?pop-types ] unit-test

{ { } { integer 1 2 } }
[ { 1 2 } { integer fixnum bool } ?pop-types ] unit-test
