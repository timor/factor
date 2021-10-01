USING: kernel math math.private tools.test types types.bn-unification ;

IN: types.tests

! Invariant:
{  }
[ [ dup drop ] infer-type ] unit-test

! Invariant:
{  }
[ [ [ drop ] keep ] infer-type ] unit-test

{ ( x: fixnum x: fixnum -- x: integer ) }
[ [ fixnum+ ] infer-type ] unit-test

{ ( x: fixnum -- x: integer ) }
[ [ 1 fixnum+ ] infer-type ] unit-test

{ ( x: fixnum -- x: integer ) }
[ [ [ 1 fixnum+ ] call ] infer-type ] unit-test

{ ( x: fixnum -- x: fixnum x: integer ) }
[ [ dup 1 fixnum+ ] infer-type ] unit-test

{ ( ..a b quot: ( ..a -- ..c ) quot: ( ..c b -- ..b ) -- ..b ) }
[ [ bi* ] infer-type ] unit-test

{ ( ..a b b3 quot: ( ..a -- ..c ) quot: ( ..c b -- ..c1 ) quot: ( ..c1 b3 -- ..b ) -- ..b ) }
[ [ tri* ] infer-type ] unit-test

{ ( ..a b quot: ( ..a -- ..c ) -- ..c b ) }
[ [ [ ] [ dip ] dip call ] infer-type ] unit-test

! FIXME: above works, this does not
{ ( ..a b quot: ( ..a -- ..c ) -- ..c b ) }
[ [ [ ] ] infer-type [ [ dip ] dip call ] infer-type unify-effects ] unit-test

{ ( ..a b quot: ( ..a -- ..c ) -- ..c b ) }
[ [ [ ] bi* ] infer-type ] unit-test

{ ( ..a x: fixnum quot: ( ..a -- ..r ) -- ..r x: integer ) }
[ [ [ 1 fixnum+ ] [ dip ] dip call ] infer-type ] unit-test

{ ( ..a x: fixnum quot: ( ..a -- ..c ) -- ..c x: integer ) }
[ [ [ 1 fixnum+ ] bi* ] infer-type ] unit-test


{ ( ..r1 b quot: ( ..r1 b -- ..c ) quot: ( ..c b -- ..b ) -- ..b ) }
[ \ bi infer-type ] unit-test

{ ( ..c b b quot: ( ..c b -- ..c ) -- ..c ) }
[ \ bi@ infer-type ] unit-test

{  }
[ [ [ ] bi@ ] infer-type ] unit-test

{  }
[ [ [ 1 fixnum+ ] bi@ ] infer-type ] unit-test
