! Copyright (C) 2025 .
! See https://factorcode.org/license.txt for BSD license.
USING: arrays choose-fail choose-fail.private continuations kernel make math
tools.test generalizations ;
IN: choose-fail.tests

: try-remaining ( quot -- )
    [ no-more-choices? ] ignore-error ; inline

! modify quot to not have any outputs, instead waiting
! for no-more-choices? being thrown
: exhaustive ( quot -- quot )
    ! dup outputs '[ _ [ dup no-more-choices? [ drop _ ndrop ] [ rethrow ] if ] recover ] ; inline
    '[ _ drop-outputs ] '[ _ [ dup no-more-choices? [ drop ] [ rethrow ] if ] recover ] ; inline

{ V{ 0 }
  f }
[ [ { 0 1 } choose , ]
  V{ } make
  cut-all paths
] unit-test

{ f
  V{ 0 1 }
  f }
[ paths 
  [
      { 0 1 } choose , [ fail ] try-remaining
  ]
  V{ } make
  paths
] unit-test


{ 0 f }
[ [ { 0 1 } choose ] with-choice paths ] unit-test

{ V{ 0 1 2 } }
[ [ [ { 0 1 2 } choose , fail
    ] exhaustive with-choice ] V{ } make ] unit-test

{ V{ 0 1 2 } }
[ [ [ { 0 1 2 3 } choose dup 3 = [ drop ] [ , fail ] if
    ] with-choice ] V{ } make ] unit-test

{ 2 }
[ [ { 0 1 2 3 } choose dup 2 = [ fail ] unless
  ] with-choice ] unit-test

[ { 0 1 2 3 } choose dup 42 = [ fail ] unless ] [ no-more-choices? ] must-fail-with


! this is similar to amb
{ { { 1 4 }
    { 1 5 }
    { 2 4 }
    { 2 5 } } }
[ [ [ { 1 2 } choose { 4 5 } choose
      2array , fail ] exhaustive { } make ] with-choice
 ] unit-test

: two-numbers ( -- num1 num2 )
    { 0 1 2 3 4 5 } choose
    { 0 1 2 3 4 5 } choose ;

: parlor-trick ( sum -- result )
    [ two-numbers ] dip 2over + =
    [ 2array ] [ 2drop fail ] if ;

{ { 2 5 } }
[ [ 7 parlor-trick ] with-choice ] unit-test

[ [ 42 parlor-trick ] with-choice ] [ no-more-choices? ] must-fail-with

{ V{ { 2 5 }
     { 3 4 }
     { 4 3 }
     { 5 2 }
   } }
[ [ [ 7 parlor-trick , fail ] exhaustive with-choice 
  ] V{ } make
] unit-test

! 22.5 descent
SYMBOLS: a b c d e eff g ;

: kids ( node -- nodes )
    { { a [ { b c } ] }
      { b [ { d e } ] }
      { c [ { d eff } ] }
      { eff [ { g } ] }
      [ drop f ]
    } case ;

: descent ( n1 n2 -- path )
    { { [ 2dup = ] [ nip 1array ] }
      { [ over kids ] [ over kids choose
                        swap descent
                        swap prefix ] }
      [ 2drop fail ]
     } cond ;

{ { a c eff g } }
[ [ a g descent ] with-choice ] unit-test

{ { a b d } }
[ [ a d descent ] with-choice ] unit-test

! each-choice triggers the fails inside the [ , ] quotation,
! while the outer try-remaining handles the fail call i
{ { { a b d }
    { a c d }
  } }
[ [ [ a d descent , fail ] exhaustive { } make ] with-choice
  ] unit-test

SYMBOLS: la ny bos ;

! :: find-boxes ( -- )
!     { la ny bos } choose :> city
!     mark nl
!     { 1 2 } choose :> store
!     { 1 2 } choose :> box
