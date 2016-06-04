! Copyright (C) 2014 John Benediktsson
! See http://factorcode.org/license.txt for BSD license

USING: kernel math namespaces ;

in: benchmark.namespaces

symbol: foo
symbol: bar
symbol: baz

: namespaces-benchmark ( -- )
    200 [
        123 foo [
            200 [
                456 bar [
                    200 [
                        789 baz [
                            foo get 123 assert=
                            bar get 456 assert=
                            baz get 789 assert=
                        ] with-variable
                    ] times
                ] with-variable
            ] times
        ] with-variable
    ] times ;

main: namespaces-benchmark
