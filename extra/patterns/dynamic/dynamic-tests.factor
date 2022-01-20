USING: kernel match math namespaces patterns.dynamic patterns.reduction
patterns.terms patterns.tests sequences tools.test ;

IN: patterns.dynamic.tests

FROM: syntax => _ ;

MATCH-VARS: ?x ?y ;

{ none }
[ M< ?x > { ?y } M< ?x >  dynamic-matching ] unit-test

SYMBOLS: a b Nil ;

CONSTANT: _elim P< [ x ] M< x > -> P< [ y ] x M< y > -> y | > | >

{ f }
[ { _elim { Cons a } { Cons a { Cons b Nil } } } pc-redex? ] unit-test

{ t }
[ { _elim { Cons a } } pc-redex? ] unit-test

assume-alpha=? off
{ t }
[ P< [ y ] { Cons a } M< y > -> y | > dup = ] unit-test

{ f }
[ P< [ y ] { Cons a } M< y > -> y | >
  P< [ y ] { Cons a } M< y > -> y | >
  = ] unit-test

assume-alpha=? on
{ t }
[ P< [ y ] { Cons a } M< y > -> y | > dup = ] unit-test

{ t }
[ P< [ y ] { Cons a } M< y > -> y | >
  P< [ y ] { Cons a } M< y > -> y | >
  = ] unit-test

{ t }
[ P< [ foo ] { Cons a } M< foo > -> foo | >
  P< [ y ] { Cons a } M< y > -> y | >
  = ] unit-test

{ P< [ y ] { Cons a } M< y > -> y | > t }
[ { _elim { Cons a } } pc-reduce-step ] unit-test

{ { Cons b Nil } }
[ { _elim { Cons a } { Cons a { Cons b Nil } } } pc-reduce ] unit-test

: seq>repr ( seq -- term )
    <reversed>
    Nil [ swap '{ Cons _ _ } ] reduce ;

PREDICATE: repr-cons < sequence { [ length 3 = ] [ first Cons = ] } 1&& ;

: repr>string ( term -- str )
    [
        [ dup repr-cons? ]
        [ first3 swap , nip ] do while
    ] "" make nip ;

{ "b" }
[ { _elim { Cons CHAR: a } } "ab" seq>repr suffix pc-reduce repr>string ] unit-test
