USING: kernel math math.private tools.test types ;

IN: types.tests

{ ( x: fixnum x: fixnum -- x: integer ) }
[ [ fixnum+ ] infer-type ] unit-test

{ ( x: fixnum -- x: integer ) }
[ [ 1 fixnum+ ] infer-type ] unit-test

{ ( x: fixnum -- x: integer ) }
[ [ [ 1 fixnum+ ] call ] infer-type ] unit-test

{ ( x: fixnum -- x: fixnum x: integer ) }
[ [ dup 1 fixnum+ ] infer-type ] unit-test

{ ( ..a1 b quot: ( ..a1 -- ..c ) quot: ( ..c b -- ..b2 ) -- ..b2 ) }
[ [ bi* ] infer-type ] unit-test

{ ( ..a1 b2 x quot: ( ..a1 -- ..c1 ) quot: ( ..c1 b2 -- ..c ) quot: ( ..c x -- ..b1 ) -- ..b1 ) }
[ [ tri* ] infer-type ] unit-test

{ ( ..a1 b quot: ( ..a1 -- ..c ) -- ..c b ) }
[ [ [ ] [ dip ] dip call ] infer-type ] unit-test

{ ( ..a b quot: ( ..a -- ..c ) -- ..c b ) }
[ [ [ ] bi* ] infer-type ] unit-test

{ ( ..a1 x: fixnum quot: ( ..a1 -- ..r ) -- ..r x: integer ) }
[ [ [ 1 fixnum+ ] [ dip ] dip call ] infer-type ] unit-test

{ ( ..a x: fixnum quot: ( ..a -- ..r1 ) -- ..r1 x: integer ) }
[ [ [ 1 fixnum+ ] bi* ] infer-type ] unit-test


! composition must work both ways
{  }
[ [ [ dip ] ] infer-type [ dip call ] infer-type unify-effects ] unit-test
{  }
[ [ [ dip ] call ] infer-type [ call ] infer-type unify-effects ] unit-test

{ ( ..r x quot: ( ..r x -- ..b ) quot: ( ..b x -- ..b2 ) -- ..b2 ) }
[ \ bi infer-type ] unit-test

{  }
[ \ bi@ infer-type ] unit-test

{  }
[ [ [ ] bi@ ] infer-type ] unit-test

{  }
[ [ [ 1 fixnum+ ] bi@ ] infer-type ] unit-test
