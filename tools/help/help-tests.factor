USING: tools.test help kernel ;
in: help.tests

[ 3 throw ] must-fail
{ } [ :help ] unit-test
{ } [ f print-topic ] unit-test
