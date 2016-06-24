! Copyright (C) 2016 Doug Coleman.
! See http://factorcode.org/license.txt for BSD license.
USING: accessors combinators.short-circuit kernel modern
modern.out sequences tools.test ;
IN: modern.out.tests

: rewrite-same-string ( string -- ? )
    [ [ ] rewrite-string ] keep sequence= ;

: rename-backtick-delimiter ( string -- string' )
    [
        dup backtick-literal? [ [ drop "^" ] change-delimiter ] when
    ] rewrite-string ;

: rename-backslash-delimiter ( string -- string' )
    [
        dup backslash-literal? [ [ drop "^" ] change-delimiter ] when
    ] rewrite-string ;

{ t } [ "fixnum`33 ch`@" rewrite-same-string ] unit-test
{ t } [ "! omg" rewrite-same-string ] unit-test
{ t } [ "todo! omg" rewrite-same-string ] unit-test
{ t } [ "foo[ bar{ baz( ) } ]" rewrite-same-string ] unit-test

{ t } [ " ARRAY: ;" rewrite-same-string ] unit-test
{ t } [ " ARRAY: 1 ;{ inline }" rewrite-same-string ] unit-test
{ t } [ " ARRAY: 1 ;[ 0 ]" rewrite-same-string ] unit-test

{ t } [ "   abc{ 1 2 3   abc}" rewrite-same-string ] unit-test
{ t } [ "  ABC: abc{ 1 2 3   abc}  ABC;" rewrite-same-string ] unit-test
{ t } [ " a{   a{   a{  a}   }   a}" rewrite-same-string ] unit-test

! Funky spaced decorator test
{ t } [
    " lol@  {    1   }@    {   2   }@    hi   @{   3    }   @{   4    }  @inline" rewrite-same-string
] unit-test
! Disable these for now.
! { t } [ " array: 1" rewrite-same-string ] unit-test
! { t } [ " {  array:  1  array:  2  }" rewrite-same-string ] unit-test



{ "fixnum^33 ch^@" } [ "fixnum`33 ch`@" rename-backtick-delimiter ] unit-test

{ "^ foo  ^    bar" } [ "\\ foo  \\    bar" rename-backslash-delimiter ] unit-test

![[
{ ": asdf < '< > > ;" } [
    ": asdf [ '[ ] ] ;" [
        dup { [ single-matched-literal? ] [ delimiter>> "[" = ] } 1&&
        [ [ drop "<" ] change-delimiter ] when
    ] rewrite-string
] unit-test
]]

! lexable-paths [ transform-single-line-comment>hash-comment ] rewrite-paths

{ t }
[ "( a: ( quot: ( b --  c   ) --  d  ) --  e  )" [ [ ] rewrite-string ] keep sequence= ] unit-test

{ t } [ "<{ ptx-2op-instruction ptx-float-ftz }" rewrite-same-string ] unit-test
{ t } [ "foo<{ ptx-2op-instruction ptx-float-ftz }" rewrite-same-string ] unit-test

{ t } [ [=[ [ dup 0 > [ number>string ] [ drop "No more" ] if ]]=] rewrite-same-string ] unit-test
{ t } [ [=[ [[omg]]]=] rewrite-same-string ] unit-test

{ t } [ "lol[[]]" rewrite-same-string ] unit-test
{ t } [ "![[]]" rewrite-same-string ] unit-test
{ t } [ "lol[[abc]]" rewrite-same-string ] unit-test
{ t } [ "![[abc]]" rewrite-same-string ] unit-test
{ t } [ "lol[==[]==]" rewrite-same-string ] unit-test
{ t } [ "![==[]==]" rewrite-same-string ] unit-test
{ t } [ "lol[==[abc]==]" rewrite-same-string ] unit-test
{ t } [ "![==[abc]==]" rewrite-same-string ] unit-test

{ t } [ "( :union{ fixnum bignum } -- )" rewrite-same-string ] unit-test
{ t } [ "data-map!( int -- float[2] )" rewrite-same-string ] unit-test
{ t } [ "a!" rewrite-same-string ] unit-test
{ t } [ "!" rewrite-same-string ] unit-test
{ t } [ "!a" rewrite-same-string ] unit-test

{ t } [ "->[ ]" rewrite-same-string ] unit-test
{ t } [ "abc>[ ]" rewrite-same-string ] unit-test
{ t } [ "CC>n" rewrite-same-string ] unit-test
{ t } [ "CC>CC" rewrite-same-string ] unit-test

{ t } [ "`omg" rewrite-same-string ] unit-test
{ t } [ "``omg``" rewrite-same-string ] unit-test
{ t } [ "```omg```" rewrite-same-string ] unit-test
{ t } [ "lol`omg" rewrite-same-string ] unit-test
{ t } [ "lol``omg``" rewrite-same-string ] unit-test
{ t } [ "lol```omg```" rewrite-same-string ] unit-test

! name = "CONSTANT" etc
:: insert-closing-semi ( tag name -- tag )
    tag dup { [ uppercase-colon-literal? ] [ tag>> name sequence= ] [ closing-tag>> not ] } 1&& [
        " ;" >>closing-tag
    ] when ;

:: remove-closing-semi ( tag name -- tag )
    tag dup { [ uppercase-colon-literal? ] [ tag>> name sequence= ] [ closing-tag>> ";" sequence= ] } 1&& [
        f >>closing-tag
    ] when ;

{ "CONSTANT: XYBitmap 0 ; ! depth 1, XYFormat" } [
    "CONSTANT: XYBitmap 0 ! depth 1, XYFormat" [
        "CONSTANT" insert-closing-semi
    ] rewrite-string
] unit-test

{ "CONSTANT: XYBitmap 0 ! depth 1, XYFormat" } [
    "CONSTANT: XYBitmap 0 ; ! depth 1, XYFormat" [
        "CONSTANT" remove-closing-semi
    ] rewrite-string
] unit-test

{ "CONSTANT: base { 3 4 5 } ;" } [
    "CONSTANT: base { 3 4 5 } ;" [
        "CONSTANT" remove-closing-semi
    ] rewrite-string [
        "CONSTANT" insert-closing-semi
    ] rewrite-string
] unit-test