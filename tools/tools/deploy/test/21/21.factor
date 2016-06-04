USING: formatting ;
in: tools.deploy.test.21

: formatting-test ( -- )
    1 2 3 "%d %d %d" printf ;

main: formatting-test
