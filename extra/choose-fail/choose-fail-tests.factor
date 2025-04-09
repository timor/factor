! Copyright (C) 2025 .
! See https://factorcode.org/license.txt for BSD license.
USING: tools.test choose-fail choose-fail.private kernel math make ;
IN: choose-fail.tests

: two-numbers ( -- num1 num2 )
    { 0 1 2 3 4 5 } choose
    { 0 1 2 3 4 5 } choose ;

: parlor-trick ( sum -- result )
    two-numbers [ + = ] 2keep
    [ '[ { "the sum of " _ _ } ] ] [ 2drop fail ] if ;

{ V{ 0 }
  f }
[
    [
        { 0 1 } choose ,
    ]
    V{ } make
    cut-all paths
] unit-test

! This unravels. The failsym on the stack is the last fail which is not captured
! by the make
{
    f
    failsym
    V{ 0 1 failsym }
    f
}
[
    paths
    [
        { 0 1 } choose , fail
    ]
    V{ } make
    paths
] unit-test
