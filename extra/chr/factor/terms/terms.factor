USING: accessors arrays chr chr.parser kernel lists prettyprint.backend
prettyprint.custom prettyprint.sections sequences ;

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
    [ tag>> cons ] [ constraint>> ] bi justify* ;

: justify ( tag constraint -- constraint )
    over nil? [ nip ] [ justify* ] if ;

TUPLE: True < type-pred cond ; constructor
TUPLE: False < type-pred cond ; constructor
TUPLE: Not < type-pred constraint ; constructor
