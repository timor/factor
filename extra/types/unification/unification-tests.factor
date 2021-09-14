! See http://factorcode.org/license.txt for BSD license.
USING: math tools.test types.unification ;
IN: types.unification.tests

{ ( ... -- ... y x ) } [ ( -- x y ) ( a b -- b a ) unify-effects ] unit-test
{ ( ..r -- ..r y x ) } [ ( ..r -- ..r x y ) ( ..s a b -- ..s b a ) unify-effects ] unit-test
{ ( ..r -- ..r y x c ) } [ ( ..r -- ..r x y ) ( ..s a b -- ..s b a c ) unify-effects ] unit-test

: c-effect-named-rows ( -- effect )
    ( ..rho a1 -- ..rho b: ( ..sigma -- ..sigma a1 ) ) ;

: c-effect-unnamed-rows ( -- effect )
    ( a1 -- b: ( -- a1 ) ) ;

: swap-effect ( -- effect )
    ( a2 b2 -- b2 a2 ) ;

{ ( ... a2 a1 -- ... quot: ( ..sigma -- ..sigma a1 ) a2 )  }
[ c-effect-named-rows swap-effect unify-effects ] unit-test

{ ( ... a2 a1 -- ... quot: ( ... -- ... a1 ) a2 ) }
[ c-effect-unnamed-rows swap-effect unify-effects ] unit-test

{ ( ..s a b x -- ..s a y b ) }
[ ( ..r x -- ..r y ) ( ..s a b c -- ..s a c b ) unify-effects ] unit-test

{ ( ... a b x -- ... a y b ) }
[ ( x -- y ) ( a b c -- a c b ) unify-effects ] unit-test

{ ( ... x: integer x: integer -- ... x: integer x: integer ) }
[ ( a: integer b: integer -- c: integer ) ( x -- x x ) unify-effects ] unit-test
