USING: compiler.tree compiler.tree.propagation.mutually-recursive.pruning
compiler.tree.propagation.mutually-recursive.tests kernel tools.test ;
IN: compiler.tree.propagation.mutually-recursive.pruning.tests

{ { f t } t } [ test-call test-if branch-with-call? ] unit-test
{ f f } [ test-call node new branch-with-call? ] unit-test
