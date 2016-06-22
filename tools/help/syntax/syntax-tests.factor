USING: kernel tools.test parser vocabs help.syntax namespaces
eval accessors ;
IN: help.syntax.tests

[
    [ "foobar" ] [
        "in: help.syntax.tests use: help.syntax about: \"foobar\"" eval( -- )
        "help.syntax.tests" lookup-vocab vocab-help
    ] unit-test

    [ { "foobar" } ] [
        "in: help.syntax.tests use: help.syntax about: { \"foobar\" }" eval( -- )
        "help.syntax.tests" lookup-vocab vocab-help
    ] unit-test

    [ ] [ "help.syntax.tests" lookup-vocab f >>help drop ] unit-test
] with-file-vocabs
