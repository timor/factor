
USING: kernel sequences tools.completion ;

in: benchmark.completion

: completion-benchmark ( -- )
    "nth" 25,000 [
        {
            nth ?nth nths set-nth insert-nth
            remove-nth remove-nth! change-nth
        }
    ] replicate concat [ name-completions ] keep
    [ length ] bi@ assert= ;

main: completion-benchmark
