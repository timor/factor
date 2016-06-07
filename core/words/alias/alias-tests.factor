USING: effects eval math tools.test ;
in: words.alias.tests

ALIAS: foo + ;
{ } [ "in: words.alias.tests CONSTANT: foo 5" eval( -- ) ] unit-test
{ ( -- value ) } [ \ foo stack-effect ] unit-test

ALIAS: \ MY-H{ \ H{ ;
{ H{ { 1 2 } } } [
    "in: words.alias.tests MY-H{ { 1 2 } }" eval( -- x )
] unit-test
