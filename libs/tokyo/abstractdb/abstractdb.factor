! Copyright (C) 2009 Bruno Deferrari
! See http://factorcode.org/license.txt for BSD license.
USING: accessors kernel tokyo.alien.tcadb tokyo.assoc-functor ;
in: tokyo.abstractdb

COMPILE< "tcadb" "abstractdb" define-tokyo-assoc-api COMPILE>

: <tokyo-abstractdb> ( name -- tokyo-abstractdb )
    tcadbnew [ swap tcadbopen drop ] keep
    tokyo-abstractdb new [ handle<< ] keep ;
