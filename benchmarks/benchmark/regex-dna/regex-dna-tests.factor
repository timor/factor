USING: benchmark.regex-dna io io.files io.encodings.ascii
io.streams.string kernel tools.test splitting ;
IN: benchmark.regex-dna.tests

{ t } [
    "vocab:benchmark/regex-dna/regex-dna-test-in.txt"
    [ regex-dna ] with-string-writer
    "vocab:benchmark/regex-dna/regex-dna-test-out.txt"
    ascii file-contents =
] unit-test
