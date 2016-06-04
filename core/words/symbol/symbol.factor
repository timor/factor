! Copyright (C) 2008 Slava Pestov.
! See http://factorcode.org/license.txt for BSD license.
USING: accessors definitions kernel sequences words ;
in: words.symbol

PREDICATE: symbol < word
    [ def>> ] [ [ ] curry ] bi sequence= ;

M: symbol definer drop \ symbol: f ;

M: symbol definition drop f ;

: define-symbol ( word -- )
    dup [ ] curry ( -- value ) define-inline ;
