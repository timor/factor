! Copyright (C) 2025 .
! See https://factorcode.org/license.txt for BSD license.
USING: accessors arrays disjoint-sets kernel literals persistent.disjoint-sets
persistent.hashtables.identity persistent.vectors tools.test variables ;
IN: persistent.disjoint-sets.tests

<<
TUPLE: foo val ;

CONSTANT: tuple-a T{ foo f "a" }
CONSTANT: tuple-b T{ foo f "a" }
CONSTANT: puf T{ persistent-union-find }
SYMBOLS: a b c d e ;
>>

{ t }
[ tuple-a tuple-b = ] unit-test

{ t }
[ puf dup clone eq? ] unit-test

{ T{ persistent-union-find f IPH{ } PV{ } PV{ } PV{ } } }
[ puf ] unit-test

{
    $ puf
    T{ persistent-union-find f IPH{ { a 0 } } PV{ a } PV{ 0 } PV{ 0 } }
}
[ puf a over added-atom ] unit-test

VAR: puf1

{ T{ persistent-union-find f IPH{ { a 0 } { b 1 } } PV{ a b } PV{ 0 0 } PV{ 0 1 } } }
[ b a puf added-atom added-atom dup set: puf1 ] unit-test

! membership
[ 42 puf representative ] [ not-a-member? ] must-fail-with
[ 42 puf1 representative ] [ not-a-member? ] must-fail-with

{ f } [ 42 puf disjoint-set-member? ] unit-test
{ f } [ 42 puf1 disjoint-set-member? ] unit-test
{ t } [ a puf1 disjoint-set-member? ] unit-test
{ { a b } } [ puf1 disjoint-set-members >array ] unit-test

VAR: puf2
{ { a b }
  { a b c d }
}
[ c puf1 added-atom d swap added-atom set: puf2
  puf1 disjoint-set-members >array
  puf2 disjoint-set-members >array
] unit-test

! equating
[ a b puf equated ] [ not-a-member? ] must-fail-with

VAR: puf3a
VAR: puf3b

! helper
: par>> ( puf -- ranks )
    parents>> >array ;

{ { 0 1 2 3 }
  { 0 0 2 3 }
  { 0 1 2 2 } }
[ a b puf2 equated set: puf3a
  c d puf2 equated set: puf3b
  puf2
  puf3a
  puf3b [ par>> ] tri@
] unit-test

{
    ! successive parents
    { 0 1 2 3 4 }
    { 0 0 2 3 4 }
    { 0 0 0 3 4 }
    { 0 0 0 0 4 }
    ! final ranks
    { 1 0 0 0 0 }
}
[ e puf2 added-atom [ par>> ] keep
  a b rot equated [ par>> ] keep
  b c rot equated [ par>> ] keep
  c d rot equated [ par>> ] keep
  ranks>> >array
] unit-test

{
    ! successive parents
    { 0 1 2 3 4 }
    { 0 1 2 2 4 }
    { 0 0 2 2 4 }
    { 0 0 0 2 4 }
    { 0 0 0 0 4 }
    ! final ranks
    { 2 0 1 0 0 }
}
[ e puf2 added-atom [ par>> ] keep
  c d rot equated [ par>> ] keep
  a b rot equated [ par>> ] keep
  b c rot equated [ par>> ] keep
  ! path compression on access
  d over representative drop [ par>> ] keep
  ranks>> >array
 ] unit-test
