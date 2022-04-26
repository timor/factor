USING: chr.factor.direct combinators.short-circuit kernel kernel.private math
prettyprint terms tools.test ;
IN: chr.factor.direct.tests

: foo ( x -- y ) 1 + ;

{  }
[ [ 1 + ] build-quot . ] unit-test

{  }
[ [ 1 + ] "haha" usym build-quot-rule . ] unit-test

{  }
[ \ foo build-word . ] unit-test

{  }
[ [ [ 1 + ] call ] build-quot . ] unit-test

{  }
[ [ [ 1 + ] call ] "hoho" usym build-quot-rule . ] unit-test

! NOTE: This may very well be equivalent to a μ-Quantifier!
{  }
[ [ dup call ] "hoho" usym build-quot-rule . ] unit-test

{  }
[ [ [ drop ] dup call ] "hoho" usym build-quot-rule . ] unit-test

! Canonical example
{  }
[ [ dup number? [ 1 + ] [ drop 0 ] if ] build-quot . ] unit-test
