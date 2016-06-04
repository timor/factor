USING: checksums checksums.md5 sequences byte-arrays kernel ;
in: benchmark.md5

: md5-benchmark ( -- )
    2000000 iota >byte-array md5 checksum-bytes drop ;

main: md5-benchmark
