USING: alien.c-types math tools.test types.typestack ;
IN: types.typestack.tests

{ { 1 } { 2 3 } }
[ { 1 2 3 } 2 pop-types ] unit-test

{ { } { 1 2 3 } }
[ { 1 2 3 } { integer fixnum bool } ?pop-types ] unit-test

{ { } { integer 1 2 } }
[ { 1 2 } { integer fixnum bool } ?pop-types ] unit-test


{ ( :object -- :object :object :object ) }
[ [ dup dup ] infer-effect ] unit-test

{ ( :object :object -- ) }
[ [ drop drop ] infer-effect ] unit-test

{ ( -- :fixnum :fixnum ) }

[ [ 1 dup ] infer-effect ] unit-test
