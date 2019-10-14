USING: compiler.tree.mutually-recursive.branch-overrides fry kernel namespaces
tools.test ;
IN: compiler.tree.propagation.mutually-recursive.branch-overrides.tests

CONSTANT: test-branch T{ #if
   { in-d { 26307459 } }
   { children { } }
   { live-branches { t t } }
 }
CONSTANT: test-in-d { 1 }

: bo-test ( quot -- quot )
    '[ [ init-branch-overrides @ ] with-scope ] ; inline

{ f } [ test-in-d (get-branch-overrides) ] bo-test unit-test

{ { t f } }
[ test-in-d { t f } (add-branch-overrides) test-in-d (get-branch-overrides) ] bo-test unit-test

{ { t f } } [
    test-in-d { t f } (add-branch-overrides)
    enter-branch-overrides-scope
    test-in-d (get-branch-overrides)
] bo-test unit-test

! Outer scopes should not be modified
{ { t t } { t f } } [
    test-in-d { t f } (add-branch-overrides)
    enter-branch-overrides-scope
    test-in-d { f t } (add-branch-overrides)
    test-in-d (get-branch-overrides)
    exit-branch-overrides-scope
    test-in-d (get-branch-overrides)
] bo-test unit-test

{ f } [
    enter-branch-overrides-scope test-in-d { t t } (add-branch-overrides)
    exit-branch-overrides-scope
    test-in-d (get-branch-overrides)
] bo-test unit-test

{ { t f } } [
    { t f } test-branch add-branch-overrides
    { 26307459 } (get-branch-overrides)
] bo-test unit-test

{ { f t } } [
    { t f } test-branch add-branch-overrides
    { t t } test-branch override-children
] bo-test unit-test

{ { f f } { f t } { t t } } [
    enter-branch-overrides-scope
    { t f } test-branch add-branch-overrides
    enter-branch-overrides-scope
    { f t } test-branch add-branch-overrides
    { t t } test-branch override-children
    exit-branch-overrides-scope
    { t t } test-branch override-children
    exit-branch-overrides-scope
    { t t } test-branch override-children
] bo-test unit-test
