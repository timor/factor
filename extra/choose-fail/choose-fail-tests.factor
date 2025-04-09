! Copyright (C) 2025 .
! See https://factorcode.org/license.txt for BSD license.
USING: tools.test choose-fail choose-fail.private kernel math make
    continuations ;
IN: choose-fail.tests

: two-numbers ( -- num1 num2 )
    { 0 1 2 3 4 5 } choose
    { 0 1 2 3 4 5 } choose ;

: parlor-trick ( sum -- result )
    [ two-numbers ] dip 2over + =
    [ '{ "the sum of " _ _ } ] [ 2drop fail ] if ;

: try-remaining ( quot -- )
    [ no-more-choices? ] ignore-error ; inline

{ V{ 0 }
  f }
[
    [
        { 0 1 } choose ,
    ]
    V{ } make
    cut-all paths
] unit-test

{
    f
    V{ 0 1 }
    f
}
[
    paths
    [
        { 0 1 } choose , [ fail ] try-remaining
    ]
    V{ } make
    paths
] unit-test


{ 0 f }
[ [ { 0 1 } choose ] with-choice paths ] unit-test

{ V{ 0 1 2 } }
[ [ [ { 0 1 2 } choose , [ fail ] try-remaining
    ] with-choice ] V{ } make ] unit-test
