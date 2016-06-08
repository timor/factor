USING: alien.libraries.finder sequences tools.test ;
in: alien.libraries.fidner.linux

{ t } [ "libm.so" "m" find-library subseq? ] unit-test
{ t } [ "libc.so" "c" find-library subseq? ] unit-test
