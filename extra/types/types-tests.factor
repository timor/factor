USING: kernel math math.private tools.test types types.bn-unification ;

IN: types.tests

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

{ ( ..a1 x: fixnum quot: ( ..a1 -- ..r ) -- ..r x: integer ) }
[ [ [ 1 fixnum+ ] [ dip ] dip call ] infer-type ] unit-test

{ ( ..a x: fixnum quot: ( ..a -- ..r1 ) -- ..r1 x: integer ) }
[ [ [ 1 fixnum+ ] bi* ] infer-type ] unit-test


{ ( ..r x quot: ( ..r x -- ..b ) quot: ( ..b x -- ..b2 ) -- ..b2 ) }
[ \ bi infer-type ] unit-test

{  }
[ \ bi@ infer-type ] unit-test

{  }
[ [ [ ] bi@ ] infer-type ] unit-test

{  }
[ [ [ 1 fixnum+ ] bi@ ] infer-type ] unit-test
