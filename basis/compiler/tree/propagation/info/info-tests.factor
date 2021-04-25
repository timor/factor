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

TUPLE: rw-tup a ;
TUPLE: mixed-tup { a read-only } b ;

{ f } [ T{ rw-tup f 42 } immutable-tuple-literal? ] unit-test
{ f } [ T{ mixed-tup f 11 22 } immutable-tuple-literal? ] unit-test
{ f } [ T{ rw-tup f T{ test-tuple f 33 } } immutable-tuple-literal? ] unit-test
{ t } [ T{ test-tuple f 42 } immutable-tuple-literal? ] unit-test
{ t } [ T{ test-tuple f T{ test-tuple f 47 } } immutable-tuple-literal? ] unit-test
{ f } [ T{ test-tuple f T{ rw-tup f 48 } } immutable-tuple-literal? ] unit-test
{ f } [ T{ test-tuple f T{ mixed-tup f 49 50 } } immutable-tuple-literal? ] unit-test

! Deliteralization
{
    T{ value-info-state
      { class rw-tup }
      { interval empty-interval }
      { slots { f T{ value-info-state { class fixnum } { interval T{ interval { from { 42 t } } { to { 42 t } } } } { literal 42 } { literal? t } } } }
    }
} [ T{ rw-tup f 42 } <literal-info> deliteralize-slots ] unit-test

{
  T{ value-info-state
     { class mixed-tup }
     { interval empty-interval }
     { slots
       {
           f
           T{ value-info-state { class fixnum } { interval T{ interval { from { 11 t } } { to { 11 t } } } } { literal 11 } { literal? t } }
           T{ value-info-state { class fixnum } { interval T{ interval { from { 22 t } } { to { 22 t } } } } { literal 22 } { literal? t } }
       }
     }
   }
} [ T{ mixed-tup f 11 22 } <literal-info> deliteralize-slots ] unit-test


{
    T{ value-info-state
       { class rw-tup }
       { interval empty-interval }
       { slots
         {
             f
             T{ value-info-state
                { class test-tuple }
                { interval empty-interval }
                { literal T{ test-tuple { x 33 } } }
                { literal? t }
                { slots { f T{ value-info-state { class fixnum } { interval T{ interval { from { 33 t } } { to { 33 t } } } } { literal 33 } { literal? t } } } }
              }
         }
       }
     }
} [ T{ rw-tup f T{ test-tuple f 33 } } <literal-info> deliteralize-slots ] unit-test

{
    T{ value-info-state
       { class test-tuple }
       { interval empty-interval }
       { slots
         {
             f
             T{ value-info-state
                { class rw-tup }
                { interval empty-interval }
                { slots { f T{ value-info-state { class fixnum } { interval T{ interval { from { 48 t } } { to { 48 t } } } } { literal 48 } { literal? t } } } }
                { origin HS{ T{ literal-allocation { literal T{ rw-tup { a 48 } } } } } }
              }
         }
       }
     }
} [ T{ test-tuple f T{ rw-tup f 48 } } <literal-info> deliteralize-slots ] unit-test

{
    T{ value-info-state
       { class test-tuple }
       { interval empty-interval }
       { slots
         {
             f
             T{ value-info-state
                { class mixed-tup }
                { interval empty-interval }
                { slots
                  {
                      f
                      T{ value-info-state { class fixnum } { interval T{ interval { from { 49 t } } { to { 49 t } } } } { literal 49 } { literal? t } }
                      T{ value-info-state { class fixnum } { interval T{ interval { from { 50 t } } { to { 50 t } } } } { literal 50 } { literal? t } }
                  }
                }
                { origin HS{ T{ literal-allocation { literal T{ mixed-tup { a 49 } { b 50 } } } } } }
              }
         }
       }
}
} [ T{ test-tuple f T{ mixed-tup f 49 50 } } <literal-info> deliteralize-slots ] unit-test

{
    T{ value-info-state
       { class rw-tup }
       { interval empty-interval }
       { literal T{ rw-tup { a T{ rw-tup { a T{ rw-tup { a 55 } } } } } } }
       { literal? t }
       { slots
         {
             f
             T{ value-info-state
                { class rw-tup }
                { interval empty-interval }
                { literal T{ rw-tup { a T{ rw-tup { a 55 } } } } }
                { literal? t }
                { slots
                  {
                      f
                      T{ value-info-state
                         { class rw-tup }
                         { interval empty-interval }
                         { literal T{ rw-tup { a 55 } } }
                         { literal? t }
                         { slots { f T{ value-info-state { class fixnum } { interval T{ interval { from { 55 t } } { to { 55 t } } } } { literal 55 } { literal? t } } } }
                       }
                  }
                }
              }
         }
       }
     }
    T{ value-info-state { class rw-tup } { interval empty-interval } { slots { f T{ lazy-info { values { 10005 } } } } } }
} [ [ T{ rw-tup f T{ rw-tup f T{ rw-tup f 55 } } } <literal-info> dup clone deliteralize-slots ] with-rw ] unit-test

{
    T{ value-info-state
       { class rw-tup }
       { interval empty-interval }
       { slots
         {
             f
             T{ value-info-state
                { class rw-tup }
                { interval empty-interval }
                { slots
                  {
                      f
                      T{ value-info-state
                         { class rw-tup }
                         { interval empty-interval }
                         { slots { f T{ value-info-state { class fixnum } { interval T{ interval { from { 55 t } } { to { 55 t } } } } { literal 55 } { literal? t } } } }
                         { origin HS{ T{ literal-allocation { literal T{ rw-tup { a 55 } } } } } }
                       }
                  }
                }
                { origin HS{ T{ literal-allocation { literal T{ rw-tup { a T{ rw-tup { a 55 } } } } } } } }
              }
         }
       }
       { origin HS{ T{ literal-allocation { literal T{ rw-tup f T{ rw-tup f T{ rw-tup f 55 } } } } } } }
     }
}
[ [ T{ rw-tup f T{ rw-tup f T{ rw-tup f 55 } } } <literal-info> maybe-deliteralize-tuple bake-info ] with-rw ] unit-test
