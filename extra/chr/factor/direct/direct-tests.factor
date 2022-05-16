USING: chr.factor.direct combinators.short-circuit kernel kernel.private math
prettyprint quotations terms tools.test ;
IN: chr.factor.direct.tests

: foo ( x -- y ) 1 + ;

{  }
[ [ 1 + ] "haha" usym build-quot-rule . ] unit-test

{  }
[ \ foo build-type . ] unit-test

{  }
[ [ [ 1 + ] call ] "hoho" usym build-quot-rule . ] unit-test

! NOTE: This may very well be equivalent to a μ-Quantifier!
{  }
[ [ dup call ] "hoho" usym build-quot-rule . ] unit-test

{  }
[ [ [ drop ] dup call ] "hoho" usym build-quot-rule . ] unit-test

! Some things to make sure
{ }
[ [ [ ] dup swapd curry ] build-type . ] unit-test

{ }
[ [ dup 1quotation ] build-type . ] unit-test

{ }
[ [ [ ] dup call ] build-type . ] unit-test


! Canonical example
{  }
[ [ dup number? [ 1 + ] [ drop 0 ] if ] build-type . ] unit-test

! logicthesis example
! Type is given: (: max : (-> ([x: Integer]  [y: Integer])
!                             (Refine [z: Integer] (and (>= z x) (>= z y)))))
: mymax ( x y -- z ) 2dup > -rot ? ;

{ }
[ \ mymax build-type . ] unit-test

! Target...
PREDICATE: ubyte < integer { [ 0 > ] [ 255 <= ] } 1&& ;

: addbytes ( x y -- z )
    + { ubyte } declare ;
