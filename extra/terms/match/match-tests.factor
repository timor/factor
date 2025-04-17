! Copyright (C) 2025 .
! See https://factorcode.org/license.txt for BSD license.
USING: choose-fail kernel math stack-checker terms.context terms.match
terms.parser tools.test ;
IN: terms.match.tests


{  }
[ 1 1 matcher* with-match ] unit-test

[ 1 2 matcher* with-match ] [ no-more-choices? ] must-fail-with

[ { 1 } 2 matcher* with-match ] [ no-more-choices? ] must-fail-with

[ 1 { 2 } matcher* with-match ] [ no-more-choices? ] must-fail-with


TUPLE: foo a b ;
TERM-VARS: ?a ?b ;

{  }
[ T{ foo f 1 2 } dup matcher* with-match ] unit-test

{  }
[ T{ foo f 1 2 } T{ foo f 1 2 } matcher* with-match ] unit-test

[ T{ foo f 1 2 } T{ foo f 4 2 } matcher* with-match ]  [ no-more-choices? ] must-fail-with

{ { 2 3 4 } }
[ [ T{ foo f 1 { 2 3 4 } } T{ foo f 1 ?a } matcher* call ?a var-value ] with-match ] unit-test

{ ( x -- ) } [ { 1 2 [ odd? ] ?a } matcher* infer ] unit-test

{ 6 }
[ [ { 1 2 5 6 } { 1 2 [ odd? ] ?a } matcher* call ?a var-value ] with-match ] choosing unit-test

[ { 1 2 4 } { 1 2 [ odd? ] } matcher* with-match ] [ no-more-choices? ] must-fail-with
