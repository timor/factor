! Copyright (C) 2005, 2008 Slava Pestov.
! See http://factorcode.org/license.txt for BSD license.
USING: system unix unix.ffi unix.ffi.linux ;
in: unix.linux

M: linux open-file [ open64 ] unix-system-call ;
