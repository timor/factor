! Copyright (C) 2008 Daniel Ehrenberg.
! See http://factorcode.org/license.txt for BSD license.
USING: io.encodings kernel ;
in: io.encodings.binary

SINGLETON: binary
M: binary <encoder> drop ; inline
M: binary <decoder> drop ; inline
