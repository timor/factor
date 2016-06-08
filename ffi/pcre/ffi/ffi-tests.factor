USING: pcre.ffi sequences splitting tools.test ;
in: pcre.ffi.tests

{ 2 } [ pcre_version " " split length ] unit-test
