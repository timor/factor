USING: cc cc.reduction tools.test cc.simple ;

IN: cc.reduction.tests

{ CCN{ [I]y.x }}
[ CCN{ ([I]x.[I]y.x)a } rewrite-ccn ] unit-test

{ CCN{ ([(I :: x ⟼ y)]y.x) } }
[ CCN{ ([I]x.[I,x]y.x)y } rewrite-ccn ] unit-test

{ CCN{ a@a } }
[ CCN{ ([I]x.x@x)a } rewrite-ccn ] unit-test

{ CCN{ True } }
[ CCN{ Zerop Zero } rewrite-ccn ] unit-test

{ CCN{ False } }
[ CCN{ Zerop One } rewrite-ccn ] unit-test

{ CCN{ One } }
[ CCN{ Length ( Cons foo Nil ) } rewrite-ccn ] unit-test

{ CCN{ False } }
[ CCN{ Zerop (Length ( Cons foo Nil )) } rewrite-ccn ] unit-test

{ CCN{ True } }
[ CCN{ Zerop (Length Nil ) } rewrite-ccn ] unit-test
