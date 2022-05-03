USING: accessors arrays chr chr.parser kernel sequences sequences.deep vectors ;

IN: chr.factor.terms

! * Common syntactic term predicates

TUPLE: type-pred < chr-pred ;

! Justifications
TUPLE: J < chr-pred tag constraint ; constructor
: <J> ( tag constraint -- constraint )
    ! [ 1array flatten ] dip J boa ;
    J boa ;
GENERIC: justify* ( tag constraint -- constraint )

M: object justify* <J> ;
M: array justify* [ justify* ] with map ;
M: vector justify* [ justify* ] with map ;
M: J justify*
    ! [ tag>> cons ] [ constraint>> ] bi justify* ;
    [ tag>> 2array flatten ] [ constraint>> ] bi justify* ;

: justify ( tag constraint -- constraint )
    over not [ nip ] [ justify* ] if ;
    ! justify* ;

TUPLE: True < type-pred cond ; constructor
TUPLE: False < type-pred cond ; constructor
TUPLE: Not < type-pred constraint ; constructor
TUPLE: In < type-pred cond ; constructor
TUPLE: Out < type-pred cond ; constructor
