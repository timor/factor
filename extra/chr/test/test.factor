USING: accessors chr.factor.composition chr.factor.util continuations debugger
io kernel math math.parser.private prettyprint sequences tools.test.private
tools.time ;

IN: chr.test

: assert-same-effect? ( term1 term2 -- )
    2dup same-effect? [ 2drop ] [ assert ] if ;

: short-time. ( n -- )
    1000000000 /f
    "" -1 3 "" "C" format-float "(" " sec)" surround print ;

! Tests if the result of the quot is isomorphic to the given test input
! Note that this is NOT order-independent at the moment
:: (chr-test) ( output input -- error/f failed? tested? )
    [ { } input [ with-datastack ] benchmark :> nanos first output assert-same-effect? nanos short-time. f f ] [ t ] recover t ;
TEST: chr-test

ERROR: expected-same-type quot1 quot2 type1 type2 ;
M:: expected-same-type error. ( e -- )
    e quot1>> :> q1
    e quot2>> :> q2
    e type1>> :> t1
    e type2>> :> t2
    "quot1: " write q1 .
    "type1: " write t1 .
    "quot2: " write q2 .
    "type2: " write t2 . ;

:: (test-same-type) ( q1 q2 -- error/f failed? tested? )
    [ q1 q2 [ get-type ] bi@ 2dup same-effect? [ 2drop f f ] [ [ q1 q2 ] 2dip expected-same-type ] if ] [ t ] recover t ;

TEST: test-same-type
