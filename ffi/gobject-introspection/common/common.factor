! Copyright (C) 2010 Anton Gorenko.
! See http://factorcode.org/license.txt for BSD license.
USING: namespaces sequences ;
in: gobject-introspection.common

symbol: current-namespace-name

symbol: implement-structs
implement-structs [ V{ } ] initialize

: implement-struct? ( c-type -- ? )
    implement-structs get-global member? ;
