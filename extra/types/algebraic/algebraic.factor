USING: accessors alien arrays byte-arrays classes classes.algebra combinators
effects hash-sets kernel lists math quotations sequences sets strings types
variants words ;

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

VARIANT: base-type
    +1+
    +0+
    atomic: { class }
    ! literal: { value class }
    quotation-type: { consumption production }
    intersection-type: { types }
    not-type: { type } ! May only hold atomic types
    union-type: { types } ! Top-level base-type in normal-form
    ;
! TUPLE: literal < atomic value ;
! C: <literal> literal

: if-null ( class null-quot else-quot -- base-type )
    pick null = [ drop nip call ]
    [ nip call ] if ; inline

DEFER: intersect-base-types
: intersect-union ( type1 union-types -- base-type )
    members [ intersect-base-types ] with map <union-type> ;

ERROR: null-here-means-error-somewhere-else ;
: error-if-null ( val -- val )
    dup null?
    [ null-here-means-error-somewhere-else ] when ;

: add-to-set ( value set -- set )
    clone [ adjoin ] keep ;

! TODO: this is just a test here, not actually performing nested intersection!
: intersect-quotation-types ( cons1 cons2 prod1 prod2 -- base-type )
    2over [ list>array ] bi@ [ intersect-base-types +0+? not ] 2all?
    [ swapd [ <quotation-type> ] 2bi@ 2array >hash-set <intersection-type> ]
    [ 4drop +0+ ] if ;

GENERIC: simplify-intersections ( type -- type )
M: type simplify-intersections ;

GENERIC: positive? ( atom -- ? )
M: atomic positive? drop t ;
M: not-type positive? drop f ;

! Checking base classes of inner intersections
: disjoint-positives? ( intersection-type -- ? )
    [ positive? ] filter
    ! Different constructors can be identified by different base-type classes here.
    ! This means that we may not use `quotation` as a valid atomic type!
    ! Any negative disjoint term can be removed
    [ class>> ] [ class-and ] map-reduce null = ;
: maybe-remove-negative ( positives negative -- type/f )
    tuck class>> '[ class>> _ classes-intersect? ] any?
    [ <not-type> ] [ drop f ] if ;

: maybe-reduce-negatives ( intersection-types -- intersection-types )
    [ positive? ] partition ! positives negatives
    dupd [ type>> maybe-remove-negative ] with map sift union ;

M: intersection-type simplify-intersections
    types>> members +0+ swap remove
    maybe-reduce-negatives
    { { [ dup empty? ] [ drop +1+ ] }
      { [ dup length 1 = ] [ first ] }
      { [ dup disjoint-positives? ] [ drop +0+ ] }
      [  >hash-set <intersection-type> ]
    } cond ;
M: union-type simplify-intersections
    types>> members [ simplify-intersections ] map
    +1+ swap remove dup empty?
    [ drop +0+ ]
    [ dup length 1 = [ first ] [ >hash-set <union-type> ] if ] if ;
M: not-type simplify-intersections
    1array >hash-set <union-type> simplify-intersections ;

DEFER: type-and
: intersect-base-types ( type1 type2 -- base-type )
    2dup [ +1+? ] either? [ dup +1+? [ drop ] [ nip ] if ]
    [
        2dup [ +0+? ] either? [ 2drop +0+ ]
        [
            over not-type? [ swap ] when
            { { atomic [ swap  ! class base-type
                         {
                             { atomic [ class-and [ +0+ ] [ <atomic> ] if-null ] }
                             ! { literal [ swapd class-and [ drop +0+ ] [ <literal> ] if-null ] }
                             { quotation-type [ rot quotation class-and [ 2drop +0+ ] [ drop <quotation-type> ] if-null ] }
                             { intersection-type [ [ <atomic> ] dip add-to-set <intersection-type> ] } ! NOTE: could perform eager checking here
                             ! NOTE: not-type is handled uniquely on rhs
                             ! { not-type [ ! class negated-base-type
                             !       <not-type> [ <atomic> ] dip 2array >hash-set <intersection-type>  ] }
                             { union-type [ [ <atomic> ] dip intersect-union ] }
                         } match ] }
              ! { literal [ rot ! value class base-type
              !             {
              !                 { atomic [ <atomic> [ <literal> ] dip intersect-base-types ] } ! symmetric to above
              !                 ! { literal [ swapd 2over = [ class-and error-if-null nip <literal> ] [ 4drop +0+ ] if ] }
              !                 { quotation-type [ 4drop +0+ ] }
              !                 { intersection-type [ [ <literal> ] dip add-to-set <intersection-type> ] }
              !                 { not-type [ [ <literal> dup ] dip intersect-base-types +0+? [ drop +0+ ] unless ] }
              !                 { union-type [ [ <literal> ] dip intersect-union ] }
              !             } match ] }
              { quotation-type [ rot ! consumption production base-type ]
                                 {
                                     { atomic [ <atomic> [ <quotation-type> ] dip intersect-base-types ] }
                                     ! { literal [ 4drop +0+ ] }
                                     { quotation-type [ swapd intersect-quotation-types ] }
                                     { intersection-type [ [ <quotation-type> ] dip add-to-set <intersection-type> ] } ! NOTE: could perform eager checking here
                                     ! { not-type [ <not-type> [ <quotation-type> ] dip 2array >hash-set <intersection-type> ] }
                                     { union-type [ [ <quotation-type> ] dip intersect-union ] }
                                 } match ] }
              { intersection-type [ swap ! intersection-types base-type
                                    {
                                        { atomic [ <atomic> [ <intersection-type> ] dip intersect-base-types ] }
                                        ! { literal [ <literal> [ <intersection-type> ] dip intersect-base-types ] }
                                        { quotation-type [ <quotation-type> [ <intersection-type> ] dip intersect-base-types ] }
                                        { intersection-type [ union <intersection-type> ] }
                                        ! { not-type [ <not-type> swap add-to-set <intersection-type> ] }
                                        { union-type [ [ <intersection-type> ] dip intersect-union ] }
                                    } match ] }
              { not-type [ swap ! not-type base-type
                           {
                               { atomic [ <atomic> [ <not-type> ] dip intersect-base-types ] }
                               ! { literal [ <literal> [ <not-type> ] dip intersect-base-types ] }
                               { quotation-type [ <quotation-type> [ <not-type> ] dip intersect-base-types ] }
                               { intersection-type [ <intersection-type> [ <not-type> ] dip intersect-base-types ] }
                               { not-type [ 2dup = [ nip <not-type> ] [ [ <not-type> ] bi@ 2array >hash-set <intersection-type> ] if ] }
                               { union-type [ [ <not-type> ] dip intersect-union ] }
                           } match ] }
              { union-type [ intersect-union ] }
             } match
        ] if
    ] if
    simplify-intersections ;

! * Back conversion from user-defined types into base types
GENERIC: >base-type ( parametric-type -- base-type )

! * Algebra interface
! This is akin to class-and, class-or, etc

! : type-and ( type type -- type )
!     class-and ;
! GENERIC: type-and ( type type -- type )
! ! Fallback is comparison on base types.  Since this is used for intersection,
! ! worst case is that types do intersect.  Thus, even if more specialized types
! ! don't intersect, in the worst case we assume they do.
! M: type type-and
!     >base-type type-and ;

! M: base-type type-and
!     over base-type?
!     [ 2dup type= [ drop ] [ intersect-base-types ] if ]
!     [ swap type-and ] if ;

M: classoid type-or class-or ;

M: base-type type-or
    2dup type= [ drop ] [ 2array <union-type> ] if ;

! TODO: wrong, needs to be defined for base classes with complements!
: types-intersect? ( type type -- ? )
    type-and +0+? not ;

: type-not ( type -- type )
    class-not ;


! * Back conversion into base classes, possibly less precise

: type>class ( base-type -- classoid )
    { { +1+ [ object ] }
      { +0+ [ null ] }
      { atomic [ ] }
      { quotation-type [ [ [ type>class f swap 2array ] map ] bi@ <effect> ] }
      { intersection-type [ type>class ] [ class-and ] map-reduce }
      { not-type [ type>class class-not ] }
      { union-type [ [ type>class ] [ class-or ] map-reduce ] }
    } match ;
