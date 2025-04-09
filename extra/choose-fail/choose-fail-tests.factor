! Copyright (C) 2025 .
! See https://factorcode.org/license.txt for BSD license.
USING: tools.test choose-fail choose-fail.private ;
IN: choose-fail.tests

: two-numbers ( -- num1 num2 )
    { 0 1 2 3 4 5 } choose
    { 0 1 2 3 4 5 } choose ;

: parlor-trick ( sum -- result )
    two-numbers [ + = ] 2keep
    [ '[ { "the sum of " _ _ } ] ] [ 2drop fail ] if ;

{ 0 0
  0 1
  1 0
  1 1
  fail
}
[ {  }  ] unit-test
