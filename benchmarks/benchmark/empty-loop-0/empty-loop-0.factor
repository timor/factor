USING: math math.private kernel sequences ;
in: benchmark.empty-loop-0

: empty-loop-0 ( n -- )
    dup 0 fixnum< [ drop ] [ 1 fixnum-fast empty-loop-0 ] if ;

: empty-loop-0-benchmark ( -- )
    50000000 empty-loop-0 ;

main: empty-loop-0-benchmark
