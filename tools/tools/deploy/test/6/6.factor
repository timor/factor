in: tools.deploy.test.6
USING: namespaces math kernel ;

symbol: x

symbol: y

: deploy-test-6 ( -- )
    1 x set-global
    2 y set-global
    x get-global y get-global + 3 assert= ;

main: deploy-test-6
