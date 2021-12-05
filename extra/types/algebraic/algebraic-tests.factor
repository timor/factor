USING: arrays classes.algebra hash-sets kernel literals math strings tools.test
types types.algebraic types.parametric.literal ;
IN: types.algebraic.tests

${ 1 <literal-type> }
[ 1 type-of ] unit-test

${ 42 <literal-type> }
[ integer 42 type-of type-and ] unit-test

{ +1+ }
[ +1+ +1+ intersect-base-types ] unit-test

{ +0+ }
[ +0+ +1+ intersect-base-types ] unit-test

{ +0+ }
[ integer <atomic> string <atomic> intersect-base-types ] unit-test

{ t }
[ fixnum <atomic> string <atomic> 2array disjoint-positives? ] unit-test

{ f }
[ fixnum <atomic> string <atomic> <not-type> 2array disjoint-positives? ] unit-test

{ f }
[ string <atomic> 1array fixnum <atomic> maybe-remove-negative ] unit-test

${ string <atomic> fixnum <atomic> 2array >hash-set }
[ string <atomic> fixnum <atomic> 2array
  maybe-reduce-negatives >hash-set
] unit-test

${ string <atomic> 1array >hash-set }
[ string <atomic> fixnum <atomic> <not-type> 2array
  maybe-reduce-negatives >hash-set
] unit-test

${ number <atomic> <not-type> }
[ tuple <atomic> 1array number <atomic> maybe-remove-negative ] unit-test

${ number <atomic> tuple <atomic> <not-type> 2array >hash-set }
[ number <atomic> tuple <atomic> <not-type> 2array
  maybe-reduce-negatives >hash-set
] unit-test

${ 42 <literal-type> }
! [ string <atomic> <not-type> 42 type-of intersect-base-types ] unit-test
[ string type-not 42 type-of class-and ] unit-test

{ null }
[ number type-not 42 type-of class-and ] unit-test

! ${ 42 type-of <not-type> }
! [ 42 type-of type-not 42 type-of type-not intersect-base-types ] unit-test

! ${ T{ intersection-type f HS{ T{ not-type f T{ literal f "asf" string } } T{ atomic f fixnum } } } }
! [ "asf" type-of type-not fixnum <atomic> intersect-base-types ] unit-test

! ${ T{ intersection-type f HS{ T{ not-type f T{ literal f "asf" string } } T{ not-type f T{ atomic f fixnum } } } } }
! [ "asf" type-of <not-type> fixnum <atomic> <not-type> intersect-base-types ] unit-test
