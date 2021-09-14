USING: kernel math math.private tools.test types ;

IN: types.tests

{ ( x: fixnum x: fixnum -- x: integer ) }
[ [ fixnum+ ] infer-type ] unit-test

{ ( ... x: fixnum -- ... x: integer ) }
[ [ 1 fixnum+ ] infer-type ] unit-test

{ ( ... x: fixnum -- ... x: integer ) }
[ [ [ 1 fixnum+ ] call ] infer-type ] unit-test

{ ( ... x: fixnum -- ... x: fixnum x: integer ) }
[ [ dup 1 fixnum+ ] infer-type ] unit-test

{ ( ..a b quot: ( ..a -- ..c ) quot: ( ..c b -- ..b ) -- ..b ) }
[ [ bi* ] infer-type ] unit-test

{  }
[ [ [ 1 fixnum+ ] [ dip ] dip call ] infer-type ] unit-test

{  }
[ [ [ 1 fixnum+ ] bi* ] infer-type ] unit-test
