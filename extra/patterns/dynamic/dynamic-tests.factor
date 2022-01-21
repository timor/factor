USING: arrays combinators.short-circuit kernel make match math math.functions
namespaces patterns.dynamic patterns.reduction patterns.terms patterns.tests
sequences tools.test typed ;

IN: patterns.dynamic.tests

USE: patterns.static

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

{ nomatch }
! NOTE: If stuck, this will be returned instead:
! { { P< [ y ] P< [ ?x ] M< ?x > -> Nil | > M< y > -> y | > Nil } }
[ _elim \ ?x Nil <dlam> Nil 3array pc-reduce ] unit-test

DEFER: elim*
CONSTANT: elim* P< [ x ] M< x > -> P< [ y ] x M< y > -> elim* x y | P< [ y ] M< y > -> y | > > | >

! Only works if inner reduction is not applied!
{ "bca" }
[ { elim* { Cons CHAR: a } } "aaabca" seq>repr suffix pc-reduce repr>string ] unit-test

SYMBOLS: Zero Successor Pair true false ;

{ b }
[ { _elim { Pair __ } { Pair a b } } pc-reduce ] unit-test

! Friggin magic... the lambda captures the ŷ from elim and basically replaces the pattern...
{ a }
[ { _elim lam{ x Pair x __ } { Pair a b } } pc-reduce ] unit-test

! Numbers

! Mixing static and dynamic patterns
! CONSTANT: isZero P< [ ] Successor __ -> false | P{ Zero -> true } >
CONSTANT: isZero P< [ ] Zero -> true | P< [ ] Successor __ -> false | > >

CONSTANT: pred P< [ tt ] Successor M< tt > -> tt | >

PREDICATE: natural < integer 0 >= ;
TYPED: num>church ( n: natural -- term )
    [ Zero ] [ Successor swap 1 - num>church 2array ] if-zero ;

DEFER: entrypattern
CONSTANT: entrypattern P< [ n ] Successor M< n > -> lam{ x Cons __ { entrypattern n x } } |
   P{ Zero -> lam{ x Cons x __ } } >

CONSTANT: entry lam{ n _elim { entrypattern n } }

{ P< [ y ] Cons __ { Cons __ { Cons M< y > __ } } -> y | > }
[ { entry } 2 num>church suffix pc-reduce ] unit-test

{ CHAR: c }
[ { entry } 2 num>church suffix "abcd" seq>repr suffix pc-reduce ] unit-test


! Views
SYMBOLS: Cart ;

CONSTANT: polar2cart P< [ r th ] Pair M< r > M< th > -> Pair { r * cos th } { r * sin th } | >
CONSTANT: cart2polar P< [ x y ] Pair M< x > M< y > ->
  Pair { sqrt { { x ^ 2 } + { y ^ 2 } } } { atan { y / x } } | >

! TODO Fix expansion
SINGLETON: view
PREDICATE: view-term < app-term head-term view? ;
M:: view-term basic-matching ( term seq pat -- result: match-result )
    pat first3 nipd :> ( fn p )
    fn term 2array pc-reduce seq p basic-matching ;

CONSTANT: complexmul P< [ r1 th1 ] view cart2polar { Pair M< r1 > M< th1 > } ->
P< [ r2 th2 ] view cart2polar { Pair M< r2 > M< th2 > } -> polar2cart { Pair { r1 * r2 } { th1 + th2 } } | > | >

SYMBOLS: x1 x2 y1 y2 ;

{
    {
        Pair
        { { { sqrt { { x1 ^ 2 } + { y1 ^ 2 } } } * { sqrt { { x2 ^ 2 } + { y2 ^ 2 } } } } * cos { { atan { y1 / x1 } } + { atan { y2 / x2 } } } }
        { { { sqrt { { x1 ^ 2 } + { y1 ^ 2 } } } * { sqrt { { x2 ^ 2 } + { y2 ^ 2 } } } } * sin { { atan { y1 / x1 } } + { atan { y2 / x2 } } } }
    }

}

[ { complexmul { Pair x1 y1 } { Pair x2 y2 } } pc-reduce ] unit-test
