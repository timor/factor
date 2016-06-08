! Copyright (C) 2010 Doug Coleman.
! See http://factorcode.org/license.txt for BSD license.
USING: combinators kernel system vocabs ;
in: time

HOOK: set-time os ( timestamp -- ) ;
HOOK: adjust-time-monotonic os ( timestamp -- seconds ) ;

{
    { [ os windows? ] [ "time.windows" ] }
    { [ os macosx? ] [ "time.macosx" ] }
    { [ os unix? ] [ "time.unix" ] }
} cond require
