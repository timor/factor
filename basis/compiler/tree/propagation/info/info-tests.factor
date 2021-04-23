USING: accessors alien arrays byte-arrays classes.algebra classes.struct
compiler.test compiler.tree.propagation.copy compiler.tree.propagation.info
io.encodings.utf8 kernel literals math math.intervals namespaces sequences
sequences.generalizations sequences.private tools.test ;
IN: compiler.tree.propagation.info.tests

{ f } [ 0.0 -0.0 eql? ] unit-test

! value-info-intersect
{ t t } [
    0 10 [a,b] <interval-info>
    5 20 [a,b] <interval-info>
    value-info-intersect
    [ class>> real class= ]
    [ interval>> 5 10 [a,b] = ]
    bi
] unit-test

{ float 10.0 t } [
    10.0 <literal-info>
    10.0 <literal-info>
    value-info-intersect
    [ class>> ] [ >literal< ] bi
] unit-test

{ null } [
    10 <literal-info>
    10.0 <literal-info>
    value-info-intersect
    class>>
] unit-test

{ fixnum 10 t } [
    10 <literal-info>
    10 <literal-info>
    value-info-union
    [ class>> ] [ >literal< ] bi
] unit-test

{ 3.0 t } [
    3 3 [a,b] <interval-info> float <class-info>
    value-info-intersect >literal<
] unit-test

{ 3 t } [
    2 3 (a,b] <interval-info> fixnum <class-info>
    value-info-intersect >literal<
] unit-test

{ T{ value-info-state f null empty-interval f f } } [
    fixnum -10 0 [a,b] <class/interval-info>
    fixnum 19 29 [a,b] <class/interval-info>
    value-info-intersect
] unit-test

TUPLE: test-tuple { x read-only } ;

{ t } [
    f f 3 <literal-info> 3array test-tuple <tuple-info> dup
    object-info value-info-intersect =
] unit-test

{ t t } [
    f <literal-info>
    fixnum 0 40 [a,b] <class/interval-info>
    value-info-union
    \ f class-not <class-info>
    value-info-intersect
    [ class>> fixnum class= ]
    [ interval>> 0 40 [a,b] = ] bi
] unit-test

! refine-value-info
{
    $[ fixnum array-capacity-interval <class/interval-info> ]
} [
    H{ { 1234 1234 } } copies set
    {
        H{
            { 1234 $[ fixnum <class-info> ] }
        }
    } value-infos set
    integer array-capacity-interval <class/interval-info> 1234
    refine-value-info
    1234 value-info
] unit-test

! value-info-union

{ 3 t } [
    3 <literal-info>
    null-info value-info-union >literal<
] unit-test

{ } [ { } value-infos-union drop ] unit-test

! interval>literal
{ 10 t } [
    fixnum 10 10 [a,b]  interval>literal
] unit-test

STRUCT: self { s self* } ;

TUPLE: tup1 foo ;

TUPLE: tup2 < tup1 bar ;

: make-slotted-info ( slot-classes class -- info )
    [ [ dup [ <class-info> ] when ] map ] dip <tuple-info> ;

! slots<=
{ t t f } [
    null-info null-info slots<=
    { byte-array } self make-slotted-info self <class-info> slots<=
    self <class-info> { byte-array } self make-slotted-info slots<=
] unit-test

! value-info<=
! ------------

! Comparing classes
{ t t } [
    byte-array c-ptr [ <class-info> ] bi@ value-info<=
    alien c-ptr [ <class-info> ] bi@ value-info<=
] unit-test

! Literals vs. classes
{ t f } [
    20 <literal-info> fixnum <class-info> value-info<=
    fixnum <class-info> 20 <literal-info> value-info<=
] unit-test

! Nulls vs. literals
{ t f } [
    null-info 3 <literal-info> value-info<=
    3 <literal-info> null-info value-info<=
] unit-test

! Fulls vs. literal
{ t } [
    10 <literal-info> f value-info<=
] unit-test

! Same class, different slots
{ t t f } [
    { byte-array } self make-slotted-info
    { c-ptr } self make-slotted-info
    value-info<=

    { byte-array byte-array } self make-slotted-info
    { } self make-slotted-info
    value-info<=

    { } self make-slotted-info
    { byte-array byte-array } self make-slotted-info
    value-info<=
] unit-test

! Slots with literals
{ f } [
    10 <literal-info> 1array array <tuple-info>
    20 <literal-info> 1array array <tuple-info>
    value-info<=
] unit-test

! Slots, but different classes
{ t } [
    null-info { f c-ptr } self make-slotted-info value-info<=
] unit-test

! Null vs. null vs. full
{ t t f } [
    null-info null-info value-info<=
    null-info f value-info<=
    f null-info value-info<=
] unit-test

! Same class, intervals
{ t f } [
    fixnum 20 30 [a,b] <class/interval-info>
    fixnum 0 100 [a,b] <class/interval-info>
    value-info<=
    fixnum 0 100 [a,b] <class/interval-info>
    fixnum 20 30 [a,b] <class/interval-info>
    value-info<=
] unit-test

! Different classes, intervals
{ t f f } [
    fixnum 20 30 [a,b] <class/interval-info>
    real 0 100 [a,b] <class/interval-info>
    value-info<=

    real 5 10 [a,b] <class/interval-info>
    integer 0 20 [a,b] <class/interval-info>
    value-info<=

    integer 0 20 [a,b] <class/interval-info>
    real 5 10 [a,b] <class/interval-info>
    value-info<=
] unit-test

! Mutable literals
{ f f } [
    [ "foo" ] <literal-info> [ "foo" ] <literal-info> value-info<=
    "hey" <literal-info> "hey" <literal-info> value-info<=
] unit-test

! Tuples
{ t f } [
    tup2 <class-info> tup1 <class-info> value-info<=
    tup1 <class-info> tup2 <class-info> value-info<=
] unit-test

! <class-info>
{ utf8 } [ utf8 <class-info> class>> ] unit-test

! init-interval
{
    T{ value-info-state
       { class array-capacity }
       { interval $[ array-capacity-interval ] }
    }
} [
    <value-info> -100 100 [a,b] >>interval array-capacity >>class
    init-interval
] unit-test

! wrap-interval
${
    full-interval
    empty-interval
    fixnum-interval
    array-capacity-interval
    array-capacity-interval
    -100 100 [a,b]
} [
    full-interval integer wrap-interval
    empty-interval integer wrap-interval
    full-interval fixnum wrap-interval
    fixnum-interval array-capacity wrap-interval
    -100 100 [a,b] array-capacity wrap-interval
    -100 100 [a,b] integer wrap-interval
] unit-test

TUPLE: box a ;
C: <box> box

TUPLE: foo { a read-only initial: 42 } b ;

! Adding slots to objects

{
    {
        T{ value-info-state { class object } { interval full-interval } { slot-refs HS{ T{ input-ref { index 0 } } } } }
        T{ value-info-state { class object } { interval full-interval } { slot-refs HS{ T{ input-ref { index 0 } } } } }
        T{ value-info-state { class object } { interval full-interval } { slot-refs HS{ T{ input-ref { index 1 } } } } }
        T{ value-info-state { class object } { interval full-interval } { slot-refs HS{ T{ input-ref { index 1 } } } } }
        T{ value-info-state
           { class object }
           { interval full-interval }
           { slot-refs HS{ T{ input-ref { index 0 } } T{ tuple-slot-ref { object-value 22 } { slot-num 2 } } } }
         }
        T{ value-info-state
           { class object }
           { interval full-interval }
           { slot-refs HS{ T{ input-ref { index 0 } } T{ tuple-slot-ref { object-value 22 } { slot-num 2 } } } }
         }
        T{ value-info-state
           { class object }
           { interval full-interval }
           { slot-refs HS{ T{ input-ref { index 1 } } T{ tuple-slot-ref { object-value 22 } { slot-num 3 } } } }
         }
        T{ value-info-state
           { class object }
           { interval full-interval }
           { slot-refs HS{ T{ input-ref { index 1 } } T{ tuple-slot-ref { object-value 22 } { slot-num 3 } } } }
         }
        T{ value-info-state { class null } { interval empty-interval } }
        T{ value-info-state { class null } { interval empty-interval } }
        T{ value-info-state
           { class foo }
           { interval full-interval }
           { slots
             {
                 f
                 T{ value-info-state
                    { class object }
                    { interval full-interval }
                    { slot-refs
                      HS{ T{ input-ref { index 0 } } T{ tuple-slot-ref { object-value 22 } { slot-num 2 } } }
                    }
                  }
                 T{ value-info-state
                    { class object }
                    { interval full-interval }
                    { slot-refs
                      HS{ T{ input-ref { index 1 } } T{ tuple-slot-ref { object-value 22 } { slot-num 3 } } }
                    }
                  }
             }
           }
         }
        T{ value-info-state
           { class foo }
           { interval full-interval }
           { slots
             {
                 f
                 T{ value-info-state
                    { class object }
                    { interval full-interval }
                    { slot-refs
                      HS{ T{ input-ref { index 0 } } T{ tuple-slot-ref { object-value 22 } { slot-num 2 } } }
                    }
                  }
                 T{ value-info-state
                    { class object }
                    { interval full-interval }
                    { slot-refs
                      HS{ T{ input-ref { index 1 } } T{ tuple-slot-ref { object-value 22 } { slot-num 3 } } }
                    }
                  }
             }
           }
         }
    }
}

[ [| |
   { 0 1 22 33 44 55 66 } introduce-values
   ! existing input value from slot 0
   object-info 0 set-value-info
   object-info 1 set-value-info
   ! #introduce assigns these to its outputs
   0 <input-ref> <slot-ref-info> 0 refine-value-info
   1 <input-ref> <slot-ref-info> 1 refine-value-info
   0 value-info dup clone
   1 value-info dup clone

   ! tuple boa call, propagate-slot-refs
   0 22 2 register-tuple-slot-storage
   0 value-info dup clone
   1 22 3 register-tuple-slot-storage
   1 value-info dup clone
   22 value-info dup clone

   ! tuple boa call, propagate-before

   { f 0 1 } foo <tuple-ref-info> 22 set-value-info ! TODO: inner?
   22 value-info dup clone
   12 narray
] with-rw ] unit-test
