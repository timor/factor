USING: kernel quotations tools.test types.typestack.generic ;
IN: types.typestack.generic.tests


{ f }
[ ( x -- x ) ( x x -- x x ) dispatch<= ] unit-test

{ t }
[ ( x x -- x x ) ( x -- x ) dispatch<= ] unit-test

{ t }
[ ( x -- x ) ( -- ) dispatch<= ] unit-test

{ t }
[ ( :quotation -- ) ( :object -- ) dispatch<= ] unit-test

{ f }
[ ( :object -- ) ( :quotation -- ) dispatch<= ] unit-test

{ t }
[ ( :object -- ) ( :object -- ) dispatch<= ] unit-test

{ f }
[ ( :object -- ) ( :object -- ) dispatch< ] unit-test

{
    0
    { ( :object -- ) [  ] [  ] }
}
[ {
        { ( :object -- ) [  ] [  ] }
        { ( :fixnum -- ) [  ] [  ] }
        { ( :integer -- ) [  ] [  ] }

    } largest-dispatch-spec ] unit-test

{
    1
    { ( :object -- ) [  ] [  ] }
}
[ {
        { ( :fixnum -- ) [  ] [  ] }
        { ( :object -- ) [  ] [  ] }
        { ( :integer -- ) [  ] [  ] }

    } largest-dispatch-spec ] unit-test

{
    {
        { ( :object -- ) [  ] [  ] }
        { ( :integer -- ) [  ] [  ] }
        { ( :fixnum -- ) [  ] [  ] }
    }
}
[ {
        { ( :object -- ) [  ] [  ] }
        { ( :fixnum -- ) [  ] [  ] }
        { ( :integer -- ) [  ] [  ] }

    } sort-dispatch-specs ] unit-test

[ {
        { ( :object -- x ) [  ] [  ] }
        { ( :object -- y ) [  ] [  ] }
        { ( :fixnum -- ) [  ] [  ] }
        { ( :integer -- ) [  ] [  ] }

    } sort-dispatch-specs ] [ dispatch-sort-failed? ] must-fail-with


{
    {
        { ( :object -- ) [  ] [  ] }
        { ( :object :object -- ) [  ] [  ] }
    }
}
[ {
        { ( :object :object -- ) [  ] [  ] }
        { ( :object -- ) [  ] [  ] }

    } sort-dispatch-specs ] unit-test
