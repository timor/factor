USING: accessors arrays assocs compiler.tree.builder compiler.tree.debugger
compiler.tree.optimizer compiler.tree.propagation
compiler.tree.propagation.inlining kernel math sequences sequences.private
slots.private tools.test ;
IN: compiler.tree.propagation.inlining.tests

{ t } [
    [ >bignum 10 mod ] build-tree propagate
    fourth dup word>> do-inlining
] unit-test

! never-inline-word?
{ t } [
    \ + props>> "default-method" of  never-inline-word?
] unit-test

! mutually-recursive inlining

TUPLE: my-seq { a array read-only } ;
M: my-seq length a>> length ; inline
M: my-seq nth-unsafe a>> nth ; inline
INSTANCE: my-seq sequence
{ slot } [ [ { 1 2 3 } my-seq boa first ] build-tree optimize-tree nodes>quot last ] unit-test

! recursion check
TUPLE: bad-seq { a array read-only } ;
M: bad-seq nth nth ; inline
{  } [ [ { 1 2 3 } bad-seq boa first ] build-tree optimize-tree drop ] unit-test
