USING: accessors furnace.auth.login tools.test ;
in: furnace.auth.login.tests

{ "Some realm" } [
    f "Some realm" <login-realm> name>>
] unit-test
