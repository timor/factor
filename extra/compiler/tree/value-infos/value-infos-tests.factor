USING: tools.test compiler.tree.value-infos ;
IN: compiler.tree.value-infos.tests

: test-value-infos ( nodes -- assoc )
    [
        drop
        tree-value-infos get
    ] with-tree-value-infos ;

: test-quot ( -- quot )
    [ { 1 2 3 } [ + ] with map ] ;

{ t } [ test-quot treeviz-tree test-value-infos hashtable? ] unit-test

{ t } [ test-quot build-tree optimize-tree test-value-infos hashtable? ] unit-test
