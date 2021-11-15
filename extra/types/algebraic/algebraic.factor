USING: accessors alien arrays byte-arrays classes classes.algebra effects kernel
math quotations sequences sets strings variants words ;

IN: types.algebraic

! Modeling factor vm values as algebraic data types

! These formalize the values which are distinguished by tags
VARIANT: object-type
    fixnum-object: { { value: fixnum } }
    f-object
    array-object: { { value: array } }
    float-object: { { value: float } }
    quotation-object: { { value: quotation } }
    bignum-object: { { value: bignum } }
    alien-object: { { value: alien } }
    tuple-object: { { value: maybe{ tuple } } }
    wrapper-object: { { value: maybe{ wrapper } } }
    byte-array-object: { { value: byte-array } }
    callstack-object: { { value: maybe{ callstack } } }
    string-object: { { value: string } }
    word-object: { { value: maybe{ word } } }
    dll-object: { { value: maybe{ dll } } }
    ;


! Use polymorphic wrapper to simplify conversion
VARIANT: syntactic-type
    any-val
    literal-val: { value class }
    declared: { value class }
    ;

VARIANT: type
    +1+
    +0+
    atomic: { class }
    literal: { value class }
    quotation-type: { consumption production }
    intersection-type: { types }
    not-type: { type }
    union-type: { types } ! Top-level type in normal-form
    ;

: if-null ( class null-quot else-quot -- type )
    pick null = [ drop nip call ]
    [ nip call ] if ; inline

DEFER: intersect-types
: intersect-union ( type1 union-types -- type )
    members [ intersect-types ] with map <union-type> ;

ERROR: null-here-means-error-somewhere-else ;
: error-if-null ( val -- val )
    dup null?
    [ null-here-means-error-somewhere-else ] when ;

: add-to-set ( value set -- set )
    clone [ adjoin ] keep ;

: intersect-types ( type1 type2 -- type )
    2dup [ +1+? ] either? [ dup +1+? [ drop ] [ nip ] if ]
    [
        2dup [ +0+? ] either? [ 2drop +0+ ]
        [
            { { atomic [ swap  ! class type
                         {
                             { atomic [ class-and [ +0+ ] [ <atomic> ] if-null ] }
                             { literal [ swapd class-and [ drop +0+ ] [ <literal> ] if-null ] }
                             { quotation-type [ rot quotation class-and [ 2drop +0+ ] [ drop <quotation-type> ] if-null ] }
                             { intersection-type [ [ <atomic> ] dip add-to-set <intersection-type> ] } ! NOTE: could perform eager checking here
                             { union-type [ [ <atomic> ] dip intersect-union ] }
                         } match ] }
              { literal [ rot ! value class type
                          {
                              { atomic [ class-and [ drop +0+ ] [ <literal> ] if-null ] } ! symmetric to above
                              { literal [ swapd 2over = [ class-and error-if-null nip <literal> ] [ 4drop +0+ ] if ] }
                              { quotation-type [ 4drop +0+ ] }
                              { intersection-type [ [ <literal> ] dip add-to-set <intersection-type> ] }
                              { union-type [ [ <literal> ] dip intersect-union ] }
                          } match ] }
              { quotation-type [ rot ! consumption production type ]
                                 {
                                 } match ] }
             } match
        ] if
    ] if ;

! Convert a value to a type, first approximation is literals
GENERIC: type-of ( thing -- type )
M: object type-of dup class-of <literal> ;

: push-type ( stack type -- stack )
    suffix ;

: pop-types ( stack n -- stack types )
    cut* ;

: push-types ( stack types -- stack )
    append ;

GENERIC: execute-type ( stack word -- stack )
M: object execute-type
    type-of push-type ;
: assert-in-effect-types ( stack types -- stack )
    [ length pop-types ]
    [ [ intersect-types ] 2map ] bi
    push-types ;
M: word execute-type
    stack-effect
    [ effect-in-types assert-in-effect-types ]
    [ in>> length pop-types ]
    [ effect-out-types swap [ +0+? ] any? [ length +0+ <array> ] when push-types ] tri
    ;
