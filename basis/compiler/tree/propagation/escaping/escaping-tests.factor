USING: accessors arrays compiler.test compiler.tree.propagation.escaping
compiler.tree.propagation.info compiler.tree.propagation.slot-refs kernel
kernel.private literals math math.intervals namespaces sequences tools.test
vectors ;
IN: compiler.tree.propagation.escaping.tests
FROM: compiler.tree.propagation.escaping => value-escapes ;


: frob-box ( x -- ) [ 1 + ] change-a drop ;
: frob-foo ( x -- ) [ 1 + ] change-b drop ;
: poke ( x -- x ) ; flushable

TUPLE: foo { a read-only initial: 42 } b ;
C: <foo> foo

: rw-literals ( quot/word -- seq )
    [ final-literals ] with-rw ;

: return-escapes? ( quot/word -- seq )
    ! [ propagated-tree last in-d>> [ resolve-copy value-escapes? ] map ] with-rw ;
    [ final-info [ value-info-escapes? ] map escaping-values get allocations get
    ] with-rw
    allocations set
    escaping-values set
    ;

{ f f }
[ [ { 111 222 } introduce-escaping-values
    111 value-escapes?
    222 value-escapes?
  ] with-values ] unit-test

{ t f }
[ [ { 111 222 } introduce-escaping-values
    111 value-escapes
    111 value-escapes?
    222 value-escapes?
  ] with-values ] unit-test

{ t t }
[ [ { 111 222 } introduce-escaping-values
    111 222 equate-values
    111 value-escapes
    111 value-escapes?
    222 value-escapes?
  ] with-values ] unit-test

{ t t }
[ [ { 111 222 } introduce-escaping-values
    111 value-escapes
    111 222 equate-values
    111 value-escapes?
    222 value-escapes?
  ] with-values ] unit-test

! ! Inputs escape
! { t t } [ [ swap ] return-escapes? first2 ] unit-test

: foo-slots ( foo -- a b ) [ a>> ] [ b>> ] bi inline ;

! ! Literals don't escape
! { f } [ [ 42 ] return-escapes? first ] unit-test
! { f } [ [ T{ foo f 42 47 } ] return-escapes? first ] unit-test
! ! Local allocations don't escape ( TODO: arrays )
! { f } [ [ foo new ] return-escapes? first ] unit-test
! { f } [ [ foo boa ] return-escapes? first ] unit-test
! { f } [ [ <foo> ] return-escapes? first ] unit-test
! ! Their slots do, though, if unknown
! { t t } [ [ foo boa [ a>> ] [ b>> ] bi ] return-escapes? first2 ] unit-test
! { t t } [ [ foo boa foo-slots ] return-escapes? first2 ] unit-test
! { t t } [ [ <foo> [ a>> ] [ b>> ] bi ] return-escapes? first2 ] unit-test
! ! Not if they are locally defined though
! { t f } [ [ 47 foo boa foo-slots ] return-escapes? first2 ] unit-test
! { t f } [ [ 47 <foo> foo-slots ] return-escapes? first2 ] unit-test
! { f f } [ [ 42 47 foo boa foo-slots ] return-escapes? first2 ] unit-test
! { f f } [ [ 42 47 <foo> foo-slots ] return-escapes? first2 ] unit-test
! { f f } [ [ foo new 42 >>b foo-slots ] return-escapes? first2 ] unit-test

! ! Declarations
! { t } [ [ { array } declare ] return-escapes? first ] unit-test
! { f } [ [ { fixnum } declare ] return-escapes? first ] unit-test

! ! Unknown values escape
: poof ( -- x ) 42 ;
: magic ( x -- x ) drop 42 ;
{ t } [ [ magic ] return-escapes? first ] unit-test
{ t } [ [ poof ] return-escapes? first ] unit-test

! ! foldable only takes non-mutable inputs per definition, so cannot propagate through
: foldable-magic (  x -- x  ) 1 + ; foldable
{ f } [ [ foldable-magic ] return-escapes? first ] unit-test

! TODO: this could be considered a propagate-after extension:  If a literal
! input was given to a foldable word
{ f f } [ [ dup foldable-magic ] return-escapes? first2 ] unit-test

! ! TODO: Handle declare! (probably expensive, maybe keep track of allocations?)



! ! Accessing slots should not let the object escape
{ f } [ [ 11 22 <foo> [ a>> ] keep ] return-escapes? first ] unit-test
{ f } [ [ 11 22 <foo> [ b>> ] keep ] return-escapes? first ] unit-test
{ f } [ [ T{ foo f 42 47 } [ a>> ] keep ] return-escapes? first ] unit-test
{ f } [ [ T{ foo f 42 47 } [ b>> ] keep ] return-escapes? first ] unit-test
{ f } [ [ T{ foo f 43 47 } [ a>> ] keep ] return-escapes? first ] unit-test
{ f } [ [ T{ foo f 43 47 } [ b>> ] keep ] return-escapes? first ] unit-test

{ V{ 42 47 } } [ [ [ 42 47 <foo> [ a>> ] [ b>> ] bi ] final-literals ] with-rw ] unit-test
{ V{ 42 47 } } [ [ [ 42 47 <foo> foo-slots ] final-literals ] with-rw ] unit-test
{ V{ 43 47 } } [ [ [ 43 47 <foo> foo-slots ] final-literals ] with-rw ] unit-test
{ V{ 42 47 } } [ [ [ T{ foo f 42 47 } [ a>> ] [ b>> ] bi ] final-literals ] with-rw ] unit-test
{ V{ 42 47 } } [ [ [ T{ foo f 42 47 } foo-slots ] final-literals ] with-rw ] unit-test
{ V{ 43 47 } } [ [ [ T{ foo f 43 47 } foo-slots ] final-literals ] with-rw ] unit-test

{
    V{
        T{ value-info-state
           { class fixnum }
           { interval T{ interval { from { 42 t } } { to { 42 t } } } }
           { literal 42 }
           { literal? t }
           { origin HS{ T{ literal-allocation { literal 42 } } T{ tuple-slot-ref { object-value 10491 } { slot-num 2 } } } }
         }
        T{ value-info-state { class object } { interval full-interval } { origin HS{ T{ tuple-slot-ref { object-value 10491 } { slot-num 3 } } } } }
    }
}
[ [ [ foo new foo-slots ] final-info ] with-values ] unit-test

! Non-escaping

{ V{ 42 47 } } [ [ [ 42 47 <foo> [ poke drop ] keep foo-slots ] final-literals ] with-rw ] unit-test

! Escaping
! FIXME: invalidation
{ T{ foo f 42 48 } } [ 42 47 <foo> [ frob-foo ] keep ] unit-test
{ 42 48 } [ 42 47 <foo> [ frob-foo ] keep [ a>> ] [ b>> ] bi ] unit-test
{ V{ 42 f } } [ [ [ 42 47 <foo> [ frob-foo ] keep [ a>> ] [ b>> ] bi ] final-literals ] with-rw ] unit-test
{ V{ 42 f } } [ [ [ 42 47 <foo> [ frob-foo ] keep foo-slots ] final-literals ] with-rw ] unit-test

TUPLE: box a ;
C: <box> box
! Nested non-escaping
{ f } [ [ 42 <box> <box> a>> a>> ] final-literals first ] unit-test
{ 42 } [ [ 42 <box> <box> a>> a>> ] rw-literals first ] unit-test

{ f } [ [ 42 <box> dup <box> a>> poke drop ] return-escapes? first ] unit-test

! Nested escape

! Boa call
{ T{ box f 43 } } [ 42 <box> dup <box> a>> frob-box ] unit-test
{ 43  } [ 42 <box> dup <box> a>> frob-box a>> ] unit-test
! FIXME
! { t }
{ f }
[ [ 42 <box> dup <box> a>> frob-box ] return-escapes? first ] unit-test

! Literals
{ T{ box f 43 } } [ T{ box f 42 } dup <box> a>> frob-box ] unit-test
{ 43 } [ T{ box f 42 } dup <box> a>> frob-box a>> ] unit-test

! FIXME
! Must be de-literalized
! { t }
{ f }
[ [ T{ box f 42 } dup <box> a>> frob-box ] return-escapes? first ] unit-test


! Set-slot
{ T{ box f 43 } } [ box new 42 >>a box new over >>a a>> frob-box ] unit-test
{ 43 } [ box new 42 >>a box new over >>a a>> frob-box a>> ] unit-test
{ t }
[ [ box new 42 >>a box new over >>a a>> frob-box ] return-escapes? first ] unit-test


! TODO: Test with mutated invalid literal
! TODO: circular escapes, nested circular escapes
