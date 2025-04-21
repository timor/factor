! Copyright (c) 2009 Samuel Tardieu.
! See See https://factorcode.org/license.txt for BSD license.
USING: arrays backtrack kernel math tools.test ;
IN: backtrack.tests

cut-amb
{ 1 } [ { 1 2 } amb ] unit-test
{ V{ { 1 2 } } } [ [ { 1 2 } ] bag-of ] unit-test
{ V{ 1 2 } } [ [ { 1 2 } amb ] bag-of ] unit-test
[ cut-amb { } amb ] must-fail
[ fail ] must-fail
{ V{ 1 10 2 20 } } [ [ { 1 2 } amb { 1 10 } amb * ] bag-of ] unit-test
{ V{ 7 -1 } } [ [ 3 4 { + - } amb-execute ] bag-of ] unit-test
{ "foo" t } [ [ "foo" t ] [ "bar" ] if-amb ] unit-test
{ "bar" f } [ [ "foo" f ] [ "bar" ] if-amb ] unit-test
{ "bar" f } [ [ "foo" fail ] [ "bar" ] if-amb ] unit-test

: amb-two-numbers ( -- num1 num2 )
    { 0 1 2 3 4 5 } amb
    { 0 1 2 3 4 5 } amb ;

: amb-two-numbers2 ( -- num1 num2 )
    { 0 1 2 3 4 5 } amb-lazy
    { 0 1 2 3 4 5 } amb-lazy ;

: amb-parlor-trick ( sum -- result )
    [ amb-two-numbers ] dip 2over + =
    [ fail ] unless
    2array ;

! 22.5 descent
SYMBOLS: a b c d e eff g ;

: amb-kids ( node -- nodes )
    { { a [ { b c } ] }
      { b [ { d e } ] }
      { c [ { d eff } ] }
      { eff [ { g } ] }
      [ drop f ]
    } case ;

! : amb-descent ( n1 n2 -- path )
!     { { [ 2dup = ] [ nip 1array ] }
!       { [ over amb-kids ] [ over amb-kids amb-lazy
!                         swap amb-descent
!                         swap prefix ] }
!       [ 2drop fail ]
!      } cond ;
:: amb-descent ( n1 n2 -- path )
    n1 n2 = [ n2 1array ] [
        n1 amb-kids :> nn
        nn [ fail ] unless
        nn amb-lazy n2 amb-descent
             n1 prefix
    ] if ;

! 22.6 cyclic graphs
: amb-neighbors ( node -- nodes )
   { { a [ { b d } ] }
     { b [ { c } ] }
     { c [ { a } ] }
     { d [ { e } ] }
     [ drop f ]
    } case ;

:: amb-path ( node1 node2 -- path )
    node1 amb-neighbors :> ns
    ns [ fail ] unless
    node2 ns in? [ { node2 } ]
    [ ns amb-lazy [ node2 amb-path ] keep prefix ]
    if ;
    ! { { [ ns not ] [ fail f ] }
    !   { [ node2 ns in? ] [ { node2 } ] }
    !   [ ns amb-lazy [ node2 amb-path ] keep prefix ]
    ! } cond ;
