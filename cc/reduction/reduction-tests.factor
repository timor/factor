USING: cc cc.reduction tools.test ;

IN: cc.reduction.tests

{ CCN{ [I]y.x }}
[ CCN{ ([I]x.[I]y.x)a } rewrite-ccn ] unit-test

{ CCN{ ([(I :: x ⟼ y)]y.x) } }
[ CCN{ ([I]x.[I,x]y.x)y } rewrite-ccn ] unit-test

{ CCN{ a@a } }
[ CCN{ ([I]x.x@x)a } rewrite-ccn ] unit-test
