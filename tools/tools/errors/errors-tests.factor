USING: compiler.errors stack-checker.errors tools.test words ;
in: tools.errors

defer: blah

{ } [
    {
        T{ compiler-error
           { error T{ do-not-compile f blah } }
           { asset blah }
        }
    } errors.
] unit-test
