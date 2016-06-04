! Copyright (C) 2009 Doug Coleman.
! See http://factorcode.org/license.txt for BSD license.
USING: kernel math math.combinatorics math.ranges sequences ;
in: benchmark.e-ratios

: calculate-e-ratios ( n -- e )
    iota [ factorial recip ] map-sum ;

: e-ratios-benchmark ( -- )
    5 [ 300 calculate-e-ratios drop ] times ;

main: e-ratios-benchmark
