USING: accessors arrays chr chr.parser kernel sequences sequences.deep sets ;

IN: chr.factor.terms

! * Common syntactic term predicates

TUPLE: type-pred < chr-pred ;

! Justifications
TUPLE: J < chr-pred tag constraint ; constructor
: <J> ( tag constraint -- constraint )
    [ 1array flatten ] dip J boa ;
GENERIC: justify ( tag constraint -- constraint )

M: object justify <J> ;
M: sequence justify [ justify ] with map ;
M: J justify
    [ tag>> swap 2array ] [ constraint>> ] bi justify ;


TUPLE: True < type-pred cond ; constructor
TUPLE: False < type-pred cond ; constructor
