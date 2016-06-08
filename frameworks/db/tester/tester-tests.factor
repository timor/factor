! Copyright (C) 2008 Doug Coleman.
! See http://factorcode.org/license.txt for BSD license.
USING: tools.test db.tester ;
in: db.tester.tests

{ } [ sqlite-test-db db-tester ] unit-test
{ } [ sqlite-test-db db-tester2 ] unit-test
