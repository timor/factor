! Copyright (C) 2025 .
! See https://factorcode.org/license.txt for BSD license.
USING: arrays choose-fail choose-fail.private combinators continuations
formatting io io.streams.string kernel make math sequences sets tools.test ;
IN: choose-fail.tests

: exhaust ( quot -- )
    [ no-more-choices? ] ignore-error ; inline

! modify quot to not have any outputs, instead waiting
! for no-more-choices? being thrown
: exhaustive ( quot -- quot )
    [ exhaust ] curry ; inline

: bag-of ( quot exemplar -- seq )
    [ exhaustive ] dip make ; inline

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
      { 0 1 } choose , [ fail ] exhaust
  ]
  V{ } make
  paths
] unit-test


{ 0 f }
[ [ { 0 1 } choose ] with-choice paths ] unit-test

{ { 0 1 2 } }
[ [ [ { 0 1 2 } choose , fail ] { } bag-of ] with-choice ] unit-test 

[ { 0 1 2 3 } choose dup 3 = [ drop ] [ , fail ] if ] must-infer

{ { 0 1 2 } }
[ [ [ { 0 1 2 3 } choose dup 3 = [ drop ] [ , fail ] if ] { } bag-of ] with-choice ] unit-test

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
      2array , fail ] { } bag-of ] with-choice
 ] unit-test

: two-numbers ( -- num1 num2 )
    { 0 1 2 3 4 5 } choose
    { 0 1 2 3 4 5 } choose ;

: parlor-trick ( sum -- result )
    [ two-numbers ] dip 2over + =
    [ 2array ] [ 2drop fail f ] if ;

{ { 2 5 } }
[ [ 7 parlor-trick ] with-choice ] unit-test

[ [ 42 parlor-trick ] with-choice ] [ no-more-choices? ] must-fail-with

{ { { 2 5 }
    { 3 4 }
    { 4 3 }
    { 5 2 }
  } }
[ [ [ 7 parlor-trick , fail ] { } bag-of
  ] with-choice
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
! while the outer exhaust handles the fail call i
{ { { a b d }
    { a c d }
  } }
[ [ [ a d descent , fail ] { } bag-of ] with-choice
  ] unit-test

SYMBOLS: la ny bos ;

: coin? ( city store box -- ? )
    3array
    { { la 1 2 } { ny 1 1 } { bos 2 2 } } in? ;

:: find-boxes-1 ( -- )
    { la ny bos } choose :> city
    nl
    { 1 2 } choose :> store
    { 1 2 } choose :> box
    city store box 3dup "(%S %S %S)" printf
    coin? [ "C" write ] when
    fail ;

{ "
(LA 1 1)(LA 1 2)C(LA 2 1)(LA 2 2)
(NY 1 1)C(NY 1 2)(NY 2 1)(NY 2 2)
(BOS 1 1)(BOS 1 2)(BOS 2 1)(BOS 2 2)C"
 }
[ [ find-boxes-1 ] exhaustive with-string-writer ] unit-test
