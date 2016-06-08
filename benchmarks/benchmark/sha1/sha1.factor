USING: checksums checksums.sha sequences byte-arrays kernel ;
in: benchmark.sha1

: sha1-benchmark ( -- )
    2000000 iota >byte-array sha1 checksum-bytes drop ;

MAIN: sha1-benchmark
