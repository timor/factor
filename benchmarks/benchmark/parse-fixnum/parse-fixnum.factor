USING: kernel math.parser sequences ;
in: benchmark.parse-fixnum

: parse-fixnum-benchmark ( -- )
    2,000,000 iota [
        [ number>string string>number ] [ assert= ] bi
    ] each ;

MAIN: parse-fixnum-benchmark
