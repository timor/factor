! Copyright (C) 2007, 2009 Slava Pestov, Daniel Ehrenberg.
! See http://factorcode.org/license.txt for BSD license.
USING: calendar eval generalizations io.streams.string kernel
math math.order memoize namespaces parser prettyprint see
sequences threads tools.test tools.time ;
in: memoize.tests

MEMO: fib ( m -- n )
    dup 1 <= [ drop 1 ] [ dup 1 - fib swap 2 - fib + ] if ;

MEMO: x ( a b c d e -- f g h i j )
    [ 1 + ] 4 ndip ;

{ 89 } [ 10 fib ] unit-test

{
    1 0 0 0 0
    1 0 0 0 0
} [
    0 0 0 0 0 x
    0 0 0 0 0 x
] unit-test

MEMO: see-test ( a -- b ) reverse ;

{ "USING: sequences ;\nin: memoize.tests\nMEMO: see-test ( a -- b ) reverse ;\n" }
[ [ \ see-test see ] with-string-writer ]
unit-test

{ } [ "in: memoize.tests : fib ( -- ) ;" eval( -- ) ] unit-test

{ "in: memoize.tests\n: fib ( -- ) ;\n" } [ [ \ fib see ] with-string-writer ] unit-test

[ sq ] ( a -- b ) memoize-quot "q" set

{ 9 } [ 3 "q" get call ] unit-test

{ t } [
    { 1/8 1/8 1/8 1/8 1/16 1/16 1/16 }
    [ MEMO[ seconds sleep ] each ] benchmark
    0.18e9 0.25e9 between?
] unit-test

