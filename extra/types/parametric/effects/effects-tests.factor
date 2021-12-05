USING: classes.algebra.private kernel math strings tools.test types
types.parametric.effects ;
IN: types.parametric.effects.tests

: te<= ( effect1 effect2 -- ? )
    ! [ type-of ] bi@ class<= ;
    [ type-of ] bi@ custom-class<= ;

{ t }
[ ( -- ) ( -- ) te<= ] unit-test

{ f }
[ ( x -- ) ( -- ) te<= ] unit-test

{ f }
[ ( -- ) ( x -- ) te<= ] unit-test

{ f }
[ ( x -- x ) ( -- ) te<= ] unit-test

{ t }
[ ( -- ) ( x -- x ) te<= ] unit-test

{ f }
[ ( -- ) ( x -- x x ) te<= ] unit-test

{ t }
[ ( -- x ) ( x -- x x ) te<= ] unit-test

{ f }
[ ( x -- x x ) ( -- x ) te<= ] unit-test

{ t }
[ ( :fixnum -- :fixnum ) ( :fixnum -- :fixnum ) te<= ] unit-test

{ t }
[ ( :fixnum -- ) ( :fixnum -- ) te<= ] unit-test

{ t }
[ ( :number -- ) ( :fixnum -- ) te<= ] unit-test

{ f }
[ ( :fixnum -- ) ( :number -- ) te<= ] unit-test

{ t }
[ ( :fixnum -- :number ) ( :fixnum -- :number ) te<= ] unit-test

{ t }
[ ( :object -- :number ) ( :fixnum -- :number ) te<= ] unit-test

{ f }
[ ( :string -- :number ) ( :fixnum -- :number ) te<= ] unit-test

{ t }
[ ( :object -- :fixnum ) ( :fixnum -- :number ) te<= ] unit-test

! NOTE: this is the only one that deviates from the semantics of effect<=
! because that only considers the effect height, not the number of taken elements
{ f }
[ ( x :integer -- x :fixnum ) ( :fixnum -- :number ) te<= ] unit-test

{ t }
[ ( :integer -- :fixnum ) ( x :fixnum -- x :number ) te<= ] unit-test

{ f }
[ ( ..a -- ..b ) ( ..a -- ..b ) te<= ] unit-test

{ f }
[ ( ..a -- ..a ) ( ..a -- ..b ) te<= ] unit-test

{ f }
[ ( -- ) ( ..a -- ..b ) te<= ] unit-test
