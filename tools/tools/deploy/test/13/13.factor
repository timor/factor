! Copyright (C) 2009 Slava Pestov.
! See http://factorcode.org/license.txt for BSD license.
USING: regexp kernel io ;
in: tools.deploy.test.13

: regexp-test ( a -- b ) <regexp> "xyz" swap matches? ;

: main ( -- ) "x.z" regexp-test "X" "Y" ? print ;

main: main
