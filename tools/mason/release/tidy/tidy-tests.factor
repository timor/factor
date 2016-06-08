USING: io.directories mason.config mason.release.tidy namespaces
sequences system tools.test ;
in: mason.release.tidy.tests

[ f ] [
    macosx target-os [
        "Factor.app" useless-files member?
    ] with-variable
] unit-test

[ t ] [
    linux target-os [
        "Factor.app" useless-files member?
    ] with-variable
] unit-test
