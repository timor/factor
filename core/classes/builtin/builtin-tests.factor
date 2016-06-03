USING: accessors kernel memory sequences tools.test words ;
in: classes.builtin.tests

{ f } [
    [ word? ] instances
    [
        [ name>> "f?" = ]
        [ vocabulary>> "syntax" = ] bi and
    ] any?
] unit-test
