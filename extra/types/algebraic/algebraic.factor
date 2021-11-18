USING: alien arrays byte-arrays classes classes.algebra hash-sets kernel lists
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
    not-type: { type } ! May only hold atomic or literals or quotations
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

! TODO: this is just a test here, not actually performing nested intersection!
: intersect-quotation-types ( cons1 cons2 prod1 prod2 -- type )
    2over [ list>array ] bi@ [ intersect-types +0+? not ] 2all?
    [ swapd [ <quotation-type> ] 2bi@ 2array >hash-set <intersection-type> ]
    [ 4drop +0+ ] if ;

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
                             { not-type [ <not-type> [ <atomic> ] dip 2array >hash-set <intersection-type> ] }
                             { union-type [ [ <atomic> ] dip intersect-union ] }
                         } match ] }
              { literal [ rot ! value class type
                          {
                              { atomic [ <atomic> [ <literal> ] dip intersect-types ] } ! symmetric to above
                              { literal [ swapd 2over = [ class-and error-if-null nip <literal> ] [ 4drop +0+ ] if ] }
                              { quotation-type [ 4drop +0+ ] }
                              { intersection-type [ [ <literal> ] dip add-to-set <intersection-type> ] }
                              { not-type [ [ <literal> dup ] dip intersect-types +0+? [ drop +0+ ] unless ] }
                              { union-type [ [ <literal> ] dip intersect-union ] }
                          } match ] }
              { quotation-type [ rot ! consumption production type ]
                                 {
                                     { atomic [ <atomic> [ <quotation-type> ] dip intersect-types ] }
                                     { literal [ 4drop +0+ ] }
                                     { quotation-type [ swapd intersect-quotation-types ] }
                                     { intersection-type [ [ <quotation-type> ] dip add-to-set <intersection-type> ] } ! NOTE: could perform eager checking here
                                     { not-type [ <not-type> [ <quotation-type> ] dip 2array >hash-set <intersection-type> ] }
                                     { union-type [ [ <quotation-type> ] dip intersect-union ] }
                                 } match ] }
              { intersection-type [ swap ! intersection-types type
                                    {
                                        { atomic [ <atomic> [ <intersection-type> ] dip intersect-types ] }
                                        { literal [ <literal> [ <intersection-type> ] dip intersect-types ] }
                                        { quotation-type [ <quotation-type> [ <intersection-type> ] dip intersect-types ] }
                                        { intersection-type [ union <intersection-type> ] }
                                        { not-type [ <not-type> swap add-to-set <intersection-type> ] }
                                        { union-type [ [ <intersection-type> ] dip intersect-union ] }
                                    } match ] }
              { not-type [ swap ! not-type type
                           {
                               { atomic [ <atomic> [ <not-type> ] dip intersect-types ] }
                               { literal [ <literal> [ <not-type> ] dip intersect-types ] }
                               { quotation-type [ <quotation-type> [ <not-type> ] dip intersect-types ] }
                               { intersection-type [ <intersection-type> [ <not-type> ] dip intersect-types ] }
                               { not-type [ 2dup = [ nip <not-type> ] [ [ <not-type> ] bi@ 2array >hash-set <intersection-type> ] if ] }
                               { union-type [ [ <not-type> ] dip intersect-union ] }
                           } match ] }
              { union-type [ intersect-union ] }
             } match
        ] if
    ] if ;

! Convert a value to a type, first approximation is literals
GENERIC: type-of ( thing -- type )
M: object type-of dup class-of <literal> ;

! * Algebra interface
! This is akin to class-and, class-or, etc

: type= ( type type -- ? )
    ! TODO
    = ;

: type-and ( type type -- type )
    2dup type= [ drop ] [ intersect-types ] if ;

: type-or ( type type -- type )
    2dup type= [ drop ] [ 2array <union-type> ] if ;


