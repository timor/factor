USING: kernel namespaces stack-checker.backend stack-checker.values
tools.test ;
in: stack-checker.values.tests

{ H{ { 3 input-parameter } } } [
    init-known-values
    input-parameter 3 set-known
    known-values get
] unit-test
