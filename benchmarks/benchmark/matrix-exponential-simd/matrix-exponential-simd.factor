USING: locals math math.combinatorics math.matrices.simd
prettyprint sequences typed ;
in: benchmark.matrix-exponential-simd

TYPED:: e^m4 ( m: matrix4 iterations: fixnum -- e^m: matrix4 )
    zero-matrix4
    iterations iota [| i |
        m i m4^n i factorial >float m4/n m4+
    ] each ;

:: matrix-exponential-simd-benchmark ( -- )
    f :> result!
    10000 [
        identity-matrix4 20 e^m4 result!
    ] times
    result . ;

main: matrix-exponential-simd-benchmark
