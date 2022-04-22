USING: chr.factor.direct kernel math prettyprint terms tools.test ;
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
