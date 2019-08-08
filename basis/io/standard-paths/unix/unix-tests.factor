! Copyright (C) 2011 Doug Coleman.
! See http://factorcode.org/license.txt for BSD license.
USING: environment io.standard-paths io.standard-paths.unix
sequences tools.test ;

{ f } [ "" find-in-path ] unit-test
{ t } [
    "ls" find-in-path not not
] unit-test

{ t } [
    "/sbin:" "PATH" os-env append "PATH" [
        "ps" find-in-path
        not not
    ] with-os-env
] unit-test
