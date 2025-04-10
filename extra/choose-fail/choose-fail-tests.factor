! Copyright (C) 2025 .
! See https://factorcode.org/license.txt for BSD license.
USING: arrays assocs choose-fail choose-fail.private combinators continuations
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

{ f } [ paths ] unit-test
[ fail ] [ not-in-choice-context? ] must-fail-with
[ { 1 2 } choose ] [ not-in-choice-context? ] must-fail-with
[ mark ] [ not-in-choice-context? ] must-fail-with
[ cut-choice ] [ not-in-choice-context? ] must-fail-with
[ { 1 2 } choose ] [ not-in-choice-context? ] must-fail-with
[ { 1 2 } bf-choose ] [ not-in-choice-context? ] must-fail-with

{ V{ 0 }
  f }
[ [ { 0 1 } choose , ] choosing
  V{ } make
  paths
] unit-test

{ f
  V{ 0 1 }
  f }
[ paths
  [
      { 0 1 } choose , [ fail ] exhaust
  ] choosing
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

[ { 0 1 2 3 } choose dup 42 = [ fail ] unless ] choosing [ no-more-choices? ] must-fail-with


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

! chocoblobs!1!
SYMBOLS: la ny bos ;

: coin? ( city store box -- ? )
    3array
    { { la 1 2 } { ny 1 1 } { bos 2 2 } } in? ;

: find-boxes-1 ( -- )
    { la ny bos } choose
    nl
    { 1 2 } choose
    { 1 2 } choose
    3dup "(%S %S %S)" printf
    coin? [ "C" write ] when
    fail ;

{ "
(LA 1 1)(LA 1 2)C(LA 2 1)(LA 2 2)
(NY 1 1)C(NY 1 2)(NY 2 1)(NY 2 2)
(BOS 1 1)(BOS 1 2)(BOS 2 1)(BOS 2 2)C"
}
[ [ find-boxes-1 ] choosing exhaustive with-string-writer ] unit-test

{ "
(LA 1 1)(LA 1 2)C
(NY 1 1)C
(BOS 1 1)(BOS 1 2)(BOS 2 1)(BOS 2 2)C"
}
: find-boxes-2 ( -- )
    { la ny bos } choose
    mark nl
    { 1 2 } choose
    { 1 2 } choose
    3dup "(%S %S %S)" printf
    coin? [ "C" write cut-choice ] when
    fail ;
[ [ find-boxes-2 ] choosing exhaustive with-string-writer ] unit-test

{ t }
[ paths empty? ] unit-test

! 22.6 cyclic graphs
: neighbors ( node -- nodes )
   { { a [ { b d } ] }
     { b [ { c } ] }
     { c [ { a } ] }
     { d [ { e } ] }
     [ drop f ]
    } case ;

:: path ( node1 node2 -- path )
    node1 neighbors :> ns
    { { [ ns not ] [ fail ] }
      { [ node2 ns in? ] [ { node2 } ] }
      [ ns bf-choose [ node2 path ] keep prefix ]
    } cond ;

{ { d e } } [ [ a e path ] with-choice ] unit-test

:: path2 ( node1 node2 -- path )
    node1 neighbors <reversed> :> ns
    { { [ ns not ] [ fail ] }
      { [ node2 ns in? ] [ { node2 } ] }
      [ ns bf-choose [ node2 path2 ] keep prefix ]
    } cond ;

{ { d e } } [ [ a e path2 ] with-choice ] unit-test

! same thing, but as factor's graph
CONSTANT: G1 H{
    { a HS{ c } }
    { b HS{ a } }
    { c HS{ b } }
    { d HS{ a } }
    { e HS{ d } }
}

:: mypath ( n1 n2 -- path )
    n2 G1 at* [ fail ] unless :> inc
    n1 inc in? [ { n2 } ]
    [ n1 inc members bf-choose mypath n2 suffix ] if ;

{ { d e } } [ [ a e path2 ] with-choice ] unit-test
! for the incoming adjacancy list, we have to end in a loop to make
! it interesting, so reverse all edges

CONSTANT: G2 H{
    { a HS{ b d } }
    { b HS{ c } }
    { c HS{ a } }
    { d HS{ e } }
}

:: mypath2 ( n1 n2 -- path )
    n2 G2 at* [ fail ] unless :> inc
    n1 inc in? [ { n2 } ]
    [ n1 inc members bf-choose mypath2 n2 suffix ] if ;

{ { d a } } [ [ e a mypath2 ] with-choice ] unit-test
{ { d a c b } } [ [ e b mypath2 ] with-choice ] unit-test
