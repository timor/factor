USING: see tools.test io.streams.string math sequences summary
words ;
in: see.tests

CONSTANT: test-const 10 ;

{ "in: see.tests\nCONSTANT: test-const 10 inline\n" }
[ [ \ test-const see ] with-string-writer ] unit-test

{ "in: sequences\nERROR: non-negative-integer-expected n ;\n" }
[ [ \ non-negative-integer-expected see ] with-string-writer ] unit-test

ALIAS: test-alias + ;

{ "USING: math ;\nin: see.tests\nALIAS: test-alias + inline\n" }
[ [ \ test-alias see ] with-string-writer ] unit-test

{ "in: see.tests ALIAS: test-alias ( x y -- z )" }
[ \ test-alias summary ] unit-test

{ } [ gensym see ] unit-test
