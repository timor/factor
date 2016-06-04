in: benchmark.euler150
USING: kernel project-euler.150 ;

: euler150-benchmark ( -- )
    euler150 -271248680 assert= ;

main: euler150-benchmark
