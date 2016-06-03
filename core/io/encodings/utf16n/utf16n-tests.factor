USING: accessors alien.data io.encodings.utf16
io.encodings.utf16n io.streams.byte-array kernel tools.test ;
in: io.encodings.utf16n.tests

: correct-endian ( obj -- ? )
    code>> little-endian? [ utf16le = ] [ utf16be = ] if ;

{ t } [ B{ } utf16n <byte-reader> correct-endian ] unit-test
{ t } [ utf16n <byte-writer> correct-endian ] unit-test
