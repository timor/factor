USING: tools.test types.bn-unification ;
IN: types.bn-unification.tests

{  }
[ ( x -- x x ) ( ..a quot: ( ..a y -- ..b ) quot: ( ..c -- ..d ) -- ..d ) effects>unifier
  drop
] unit-test
