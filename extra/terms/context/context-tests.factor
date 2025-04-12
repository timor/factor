! Copyright (C) 2025 .
! See https://factorcode.org/license.txt for BSD license.
USING: tools.test terms.context ;
IN: terms.context.tests


! nested scope
{ t }
[ [ 1 2 equate-vars [ 1 2 vars-equiv? ] with-equiv-scope ] with-equiv-scope ] unit-test

{ t
  t
  f }
[ [ 1 2 equate-vars { 3 4 } add-vars
    [ 3 4 equate-vars 1 2 vars-equiv? 3 4 vars-equiv? ] with-equiv-scope
    3 4 vars-equiv? ] with-equiv-scope
] unit-test
