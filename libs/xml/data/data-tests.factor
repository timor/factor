USING: assocs tools.test ;
in: xml.data

{ "bob" } [ "test" { { "name" "bob" } } { } <tag> "name" of ] unit-test
