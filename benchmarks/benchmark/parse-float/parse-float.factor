USING: kernel literals math.functions math.parser random
sequences ;
in: benchmark.parse-float

CONSTANT: test-floats $[ 100,000 random-units ]

: parse-float-benchmark ( -- )
    test-floats [
        [ number>string string>number ] [ 1e-10 ~ t assert= ] bi
    ] each ;

MAIN: parse-float-benchmark
