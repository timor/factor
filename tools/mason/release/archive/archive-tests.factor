USING: system tools.test ;

in: mason.release.archive

{ ".dmg" } [ macosx extension ] unit-test
{ ".dmg" } [ "macosx" extension ] unit-test

{ ".zip" } [ windows extension ] unit-test
{ ".zip" } [ "windows" extension ] unit-test

{ ".tar.gz" } [ unix extension ] unit-test
{ ".tar.gz" } [ "unix" extension ] unit-test

{ ".tar.gz" } [ linux extension ] unit-test
{ ".tar.gz" } [ "linux" extension ] unit-test

{ ".tar.gz" } [ f extension ] unit-test
