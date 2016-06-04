USING: arrays bit-arrays byte-arrays compiler.units definitions
tools.test ;
in: definitions.tests

GENERIC: some-generic ( a -- b ) ;

use: arrays

M: array some-generic ;

use: bit-arrays

M: bit-array some-generic ;

use: byte-arrays

M: byte-array some-generic ;

TUPLE: some-class ;

M: some-class some-generic ;

{ } [
    [
        \ some-generic
        \ some-class
        2array
        forget-all
    ] with-compilation-unit
] unit-test
