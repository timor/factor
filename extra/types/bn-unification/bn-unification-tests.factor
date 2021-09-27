USING: kernel tools.test types types.bn-unification ;
IN: types.bn-unification.tests

{  }
[ ( x -- x x ) ( ..a quot: ( ..a y -- ..b ) quot: ( ..c -- ..d ) -- ..d ) effects>unifier
  3drop
] unit-test

! composition must work both ways
{ ( ..a b quot: ( ..a -- ..c ) quot: ( ..c b -- ..b ) -- ..b ) }
[ [ [ dip ] ] infer-type [ dip call ] infer-type unify-effects ] unit-test
{ ( ..a b quot: ( ..a -- ..c ) quot: ( ..c b -- ..b ) -- ..b ) }
[ [ [ dip ] dip ] infer-type [ call ] infer-type unify-effects ] unit-test


{ ( -- b a ) } [ ( -- x y ) ( a b -- b a ) unify-effects ] unit-test
{ ( -- b a ) } [ ( ..r -- ..r x y ) ( ..s a b -- ..s b a ) unify-effects ] unit-test
{ ( -- x: fixnum x: integer ) } [ ( ..r -- ..r x: integer y: fixnum ) ( ..s a b -- ..s b a ) unify-effects ] unit-test
{ ( -- b a c ) } [ ( ..r -- ..r x y ) ( ..s a b -- ..s b a c ) unify-effects ] unit-test

: c-effect-named-rows ( -- effect )
    ( ..rho a1 -- ..rho b: ( ..sigma -- ..sigma a1 ) ) ;

: c-effect-unnamed-rows ( -- effect )
    ( a1 -- b: ( -- a1 ) ) ;

: swap-effect ( -- effect )
    ( a2 b2 -- b2 a2 ) ;

! { {  } }
! [ c-effect-named-rows swap-effect effects-unifier ] unit-test

{ ( a2 a1 -- quot: ( -- a1 ) a2 ) }
[ c-effect-named-rows swap-effect unify-effects ] unit-test

{ ( a2 a1 -- quot: ( -- a1 ) a2 ) }
[ c-effect-unnamed-rows swap-effect unify-effects ] unit-test

{ ( ..a -- ..c ) }
[ ( ..a -- ..b ) ( ..b -- ..c ) unify-effects ] unit-test

{ ( ..a -- ..c ) }
[ ( ..a -- ..b ) ( ..d -- ..c ) unify-effects ] unit-test

! NOTE: non-constrained
{ ( a b x -- a c b ) }
[ ( ..r x -- ..r y ) ( ..s a b c -- ..s a c b ) unify-effects ] unit-test

! NOTE: non-constrained
{ ( a b x -- a c b ) }
[ ( x -- y ) ( a b c -- a c b ) unify-effects ] unit-test

{ ( x: integer x: integer -- x: integer x: integer ) }
[ ( a: integer b: integer -- c: integer ) ( x -- x x ) unify-effects ] unit-test

{ ( -- x: integer ) }
[ ( -- x: integer ) ( a -- a ) unify-effects ] unit-test

{ ( x: integer -- x: integer ) }
[ ( x: integer -- y ) ( a -- a: integer ) unify-effects ] unit-test

{ ( -- x: integer x: integer ) }
[ ( -- x: integer ) ( a -- a a ) unify-effects ] unit-test

{ ( x: integer -- x: integer x: integer ) }
[ ( a -- a a ) ( x: integer -- y: integer ) unify-effects ] unit-test

! Ensure correct abstraction for duplicated nested effects
! NOTE: This does NOT re-instantiate right now!
! { ( -- quot: ( ..b1 -- ..c quot: ( ..a1 -- ..b1 ) ) quot: ( ..b2 -- ..c quot: ( ..a2 -- ..b2 ) ) ) }
{ ( -- quot: ( ..b -- ..c quot: ( ..a -- ..b ) ) quot: ( ..b -- ..c quot: ( ..a -- ..b ) ) ) }
[
    ( -- quot: ( ..b -- ..c quot: ( ..a -- ..b ) ) ) ( x -- x x ) unify-effects
] unit-test


{ ( ..a b quot: ( ..a -- ..c ) -- ..c b quot: ( -- ) ) }
[
    ( ..1 -- ..1 quot: ( ... -- ... ) quot: ( ..a b quot: ( ..a -- ..c ) -- ..c b ) )
    ( ..a b quot: ( ..a -- ..c ) -- ..c b )
    unify-effects ] unit-test

! bi@

! neuralgic point:
{ ( ..c b b quot: ( ..c b -- ..c ) -- ..c ) }
[ ( x -- x x ) ( ..a b quot: ( ..a -- ..c  ) quot: ( ..c b -- ..b2 ) -- ..b2 ) unify-effects ] unit-test

! Fully expanded:
! [ dup [ dip ] dip call ]
! Correct effect of bi@:
! ( ..a b b quot: ( ..c b -- ..d ) -- ..d )

! trying all combinations
! all wrong for now
! TODO check
: bi@-unifications ( -- )
    "1" print
    [ dup ] [ [ dip ] dip call ] [ infer-type ] bi@ unify-effects .
    "2" print
    [ dup [ dip ] ] [ dip call ] [ infer-type ] bi@ unify-effects .
    "3" print
    [ dup [ dip ] dip ] [ call ] [ infer-type ] bi@ unify-effects .
    ;

! Returns wrong result
: bi@-unis-foldr ( -- effect )
    [ dup [ dip ] dip call ]
    <reversed> [ type-of ] [ swap unify-effects dup . ] map-reduce ;

! Working intermediate goal, which would work if
! [ dup ] [ [ dip ] dip call ] had been inferred like follows, or the
! quantification rules interpreted accordingly.  The important thing could be
! that the ..c should not be considered quantified when reading the second
! quotation.  Otherwise we are establishing a constraint between an output of a
! quotation and an input of one, which can lead to recursion.
{ ( ..c b1 b1 quot: ( ..c b1 -- ..d  ) -- ..d ) }
[ ( x -- x x ) ( ..a b1 quot: ( ..a -- ..d ) quot: ( ..c b1 -- ..b ) -- ..b ) unify-effects ] unit-test

! Broken version:
{ ( ..c b1 b1 quot: ( ..c b1 -- ..c  ) -- ..c ) }
[ ( x -- x x ) ( ..a b1 quot: ( ..a -- ..c ) quot: ( ..c b1 -- ..b ) -- ..b )
  unify-effects ] unit-test

{ ( ..c d d quot: ( ..c d -- ..c ) -- ..c ) }
[ ( x -- x x )
  ( ..a1 d quot: ( ..a1 -- ..c ) quot: ( ..c d -- ..b2 ) -- ..b2 )
  unify-effects
] unit-test

{ ( ..c b b quot: ( ..c b -- ..c ) -- ..c ) }
[ ( x -- x x )
  ( ..a1 b quot: ( ..a1 -- ..c ) quot: ( ..c b -- ..b2 ) -- ..b2 )
  unify-effects
] unit-test

