USING: accessors arrays chr chr.parser classes.tuple kernel sequences
sequences.deep sets terms vectors ;

IN: chr.factor.terms

! * Common syntactic term predicates

TUPLE: type-pred < chr-pred ;
TUPLE: val-pred < type-pred val ;

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

! ** Free and bound vars
GENERIC: bound-vars ( pred -- vars )
M: object bound-vars drop f ;
M: array bound-vars [ bound-vars ] gather ;
M: vector bound-vars [ bound-vars ] gather ;
M: tuple bound-vars tuple-slots bound-vars ;
GENERIC: free-vars ( pred -- vars )
M: chr-pred free-vars
    constraint-args free-vars ;
M: array free-vars [ free-vars ] gather ;
M: vector free-vars [ free-vars ] gather ;
M: term-var free-vars dup ?ground-value 2dup eq? [ drop 1array ] [ nip free-vars ] if ;
M: object free-vars drop f ;
M: tuple free-vars tuple-slots free-vars ;

! ** Reasoning
TUPLE: True < type-pred cond ; constructor
TUPLE: False < type-pred cond ; constructor
TUPLE: Not < type-pred constraint ; constructor
TUPLE: In < type-pred cond ; constructor
TUPLE: Out < type-pred cond ; constructor
TUPLE: And < type-pred lhs rhs result ; constructor
! TUPLE: Xor < type-pred lhs rhs ; constructor
TUPLE: Xor < type-pred lhs rhs res ; constructor

! Deferred
TUPLE: Apply < chr-pred in out constraints ; constructor

TUPLE: Case < chr-pred cond preds ; constructor

! Common
TUPLE: Eval < chr-pred word in out ;
! TUPLE: Literal < chr-pred var value ;
TUPLE: Literal < val-pred value ;

! ** Lambda Fragment
! These are in return positions, and thus can form nested expression trees

! A typed definition
TUPLE: Data < chr-pred tag ; constructor
