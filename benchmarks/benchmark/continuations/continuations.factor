USING: math kernel continuations ;
in: benchmark.continuations

: continuations-benchmark ( -- )
    1,000,000 [ drop [ continue ] callcc0 ] each-integer ;

main: continuations-benchmark
