USING: arrays combinators.sequential kernel math sequences tools.test ;
IN: combinators.sequential.tests

{ 69 }
[ +start+ 42 [ 2array ] 69 skip-start call ] unit-test

{ { 41 42 } }
[ 41 42 [ 2array ] 69 skip-start call ] unit-test

{ 70 }
[ 42 +end+ [ 2array ] 70 skip-end call ] unit-test

{ { 42 43 } }
[ 42 43 [ 2array ] 70 skip-end call ] unit-test

{ { 0.5 0.25 0.125 0.0625 0.03125 0.015625 0.0078125 } }
[ { 0 0 0 0 0 0 0 } [ + 0.5 * dup ] 1 with-feedback map ] unit-test

{ { 0 0 1 0 } }
[ { 1 0 0 0 } [ ] 0 with-feedback 0 with-feedback map ] unit-test


: fir ( seq -- quot )
    [ '[ [ [ _ * + ] keep dup ] 0 with-feedback ] ] [ ] map-compose-reduce ; inline
