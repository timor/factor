! Copyright (C) 2025 .
! See https://factorcode.org/license.txt for BSD license.
USING: choose-fail classes.algebra kernel literals math stack-checker
terms.context terms.match terms.match.private terms.parser tools.test ;
IN: terms.match.tests


{  }
[ 1 1 matcher* with-match ] unit-test

[ 1 2 matcher* with-match ] [ no-more-choices? ] must-fail-with

[ { 1 } 2 matcher* with-match ] [ no-more-choices? ] must-fail-with

[ 1 { 2 } matcher* with-match ] [ no-more-choices? ] must-fail-with

[ V{ 1 2 } { 1 2 } matcher* with-match ] [ no-more-choices? ] must-fail-with

[ { 1 2 } V{ 1 2 } matcher* with-match ] [ no-more-choices? ] must-fail-with

[ [ 1 2 ] V{ 1 2 } matcher* with-match ] [ no-more-choices? ] must-fail-with

{  }
[ { 1 2 } { 1 2 } matcher* with-match ] unit-test

{  }
[ V{ 1 2 } V{ 1 2 } matcher* with-match ] unit-test

{  }
[ [ 1 2 ] [ 1 2 ] matcher* with-match ] unit-test

TUPLE: foo a b ;
TERM-VARS: ?a ?b ?c ?d ;

{  }
[ T{ foo f 1 2 } dup matcher* with-match ] unit-test

{  }
[ T{ foo f 1 2 } T{ foo f 1 2 } matcher* with-match ] unit-test

[ T{ foo f 1 2 } T{ foo f 4 2 } matcher* with-match ]  [ no-more-choices? ] must-fail-with

{ { 2 3 4 } }
[ [ T{ foo f 1 { 2 3 4 } } T{ foo f 1 ?a } matcher* call ?a var-value ] with-match ] unit-test

{ ( x -- ) } [ { 1 2 ?[ odd? ] ?a } matcher* infer ] unit-test

{ 6 }
[ [ { 1 2 5 6 } { 1 2 ?[ odd? ] ?a } matcher* call ?a var-value ] with-match ] choosing unit-test

[ { 1 2 4 } { 1 2 ?[ odd? ] } matcher* with-match ] [ no-more-choices? ] must-fail-with

! And match
{ ( x -- ) }
[ &( ?a ?[ 8 = ] ) matcher* infer ] unit-test

{ 8 }
[ 8 &( ?a ?[ 8 = ] ) matcher* [ ?a var-value ] compose with-match ] unit-test

{ 8 }
[ { 8 } { &( ?a ?[ 8 = ] ) } matcher* [ ?a var-value ] compose with-match ] unit-test

! ! As match
! { 5 { 7 8 } 7 8 }
! [ { 5 { 7 8 } } { ?a As( ?b { ?c ?d } ) } matcher* [ ?a var-value ?b var-value ?c var-value ?d var-value ] compose with-match ] unit-test

! [ { 5 { 7 8 } } { ?a As( ?b { ?a ?c } ) } matcher* [ ?a var-value ?b var-value ?c var-value ] compose with-match ]
! [ no-more-choices? ] must-fail-with

! { 5 { 5 8 } 8 }
! [ { 5 { 5 8 } } { ?a As( ?b { ?a ?c } ) } matcher* [ ?a var-value ?b var-value ?c var-value ] compose with-match ] unit-test

! Using and-match
{ 5 { 7 8 } 7 8 }
[ { 5 { 7 8 } } { ?a &( ?b { ?c ?d } ) } matcher* [ ?a var-value ?b var-value ?c var-value ?d var-value ] compose with-match ] unit-test

[ { 5 { 7 8 } } { ?a &( ?b { ?a ?c } ) } matcher* [ ?a var-value ?b var-value ?c var-value ] compose with-match ]
[ no-more-choices? ] must-fail-with

{ 5 { 5 8 } 8 }
[ { 5 { 5 8 } } { ?a &( ?b { ?a ?c } ) } matcher* [ ?a var-value ?b var-value ?c var-value ] compose with-match ] unit-test

! Tuple templates

TUPLE: bar < foo c ;

{ 1 2 }
[ T{ foo f 1 2 } _T{ foo ?a ?b } matcher* [ ?a var-value ?b var-value ] compose with-match ] unit-test

[ T{ foo f 1 2 } _T{ bar ?a ?b } matcher* [ ?a var-value ?b var-value ] compose with-match ] [ no-more-choices? ] must-fail-with

{ 1 2 }
[ T{ bar f 1 2 3 } _T{ ?[ foo class<= ] ?a ?b } matcher* [ ?a var-value ?b var-value ] compose with-match ] unit-test

! Using call matcher
{ ( x -- ) }
[ &( ?[ foo? ] $[ { 1 2 3 } slots-matcher <call-matcher> ] ) matcher* infer ] unit-test

{  }
[ T{ bar f 1 2 3 } &( ?[ foo? ] $[ { 1 2 3 } slots-matcher <call-matcher> ] ) matcher* call ] matching unit-test
