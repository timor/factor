USING: accessors assocs compiler compiler.tree.propagation.info
compiler.tree.propagation.output-infos compiler.units kernel kernel.private math
namespaces sequences tools.annotations tools.test words ;
IN: compiler.tree.propagation.output-infos.tests

! TODO: insert missing unit test!


! * Nested Compilation

: with-watched-words ( words quot -- )
    [ drop [ watch ] each ]
    [ nip call ]
    [ drop [ reset ] each ] 2tri ; inline

: test-output-infos ( words -- infos )
    [
        { compile-word maybe-compile-word check-copied-output-infos }
        [ recompile ] with-watched-words
        drop ]
    [ [ dup "output-infos" word-prop ] map>alist ] bi ;

: fun1 ( x -- y ) { fixnum } declare 3 + ;

: fun2 ( x -- y ) fun1 ;

{ } [ { fun1 fun2 } recompile drop ] unit-test

{ t } [ { fun2 fun1 } test-output-infos values first first object-info = ] unit-test

{ integer } [ { fun1 fun2 } test-output-infos values second first class>> ] unit-test

{ } [ nested-compilation? [ { fun1 fun2 } recompile drop ] with-variable-on ] unit-test
