USING: kernel tools.test definitions compiler.units ;
in: compiler.tests.redefine21

[ ] [ : a ( -- ) ; << : b ( quot -- ) call a ; inline COMPILE> [ ] b ] unit-test

[ ] [ [ { a b } forget-all ] with-compilation-unit ] unit-test

[ ] [ : A ( -- ) ; << : B ( -- ) A ; inline COMPILE> B ] unit-test

[ ] [ [ { A B } forget-all ] with-compilation-unit ] unit-test
