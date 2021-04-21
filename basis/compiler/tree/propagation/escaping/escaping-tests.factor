USING: accessors arrays compiler.test compiler.tree.propagation.escaping
compiler.tree.propagation.info compiler.tree.propagation.slot-refs kernel
kernel.private literals math math.intervals namespaces sequences tools.test
vectors ;
IN: compiler.tree.propagation.escaping.tests


: frob ( x -- ) drop ;
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
! : poof ( -- x ) 42 ;
! : magic ( x -- x ) drop 42 ;
! { t } [ [ magic ] return-escapes? first ] unit-test
! { t } [ [ poof ] return-escapes? first ] unit-test

! ! foldable only takes non-mutable inputs per definition, so cannot propagate through
! : foldable-magic (  x -- x  ) 1 + ; foldable
! { f } [ [ foldable-magic ] return-escapes? first ] unit-test

! ! TODO: this could be considered a propagate-after extension:  If a literal
! ! input was given to a foldable word
! { t f } [ [ dup foldable-magic ] return-escapes? first2 ] unit-test

! ! TODO: Handle declare! (probably expensive, maybe keep track of allocations?)



! Escaping tuple escapes
! { t } [ [ 11 22 <foo> [ frob ] keep ] return-escapes? first ] unit-test
{ T{ value-info-state
     { class foo }
     { interval full-interval }
     { slots { f
               T{ value-info-state
                  { class fixnum }
                  { interval T{ interval { from { 11 t } } { to { 11 t } } } }
                  { literal 11 }
                  { literal? t }
                  { slot-refs HS{ T{ tuple-slot-ref { object-value 10005 } { slot-num 2 } } } } }
               f } } }
 } [ [ [ 11 22 <foo> [ frob ] keep ] final-info first ] with-rw ] unit-test

! Non-escaping
{ f } [ [ 11 22 <foo> [ poke drop ] keep ] return-escapes? first ] unit-test
{
    T{ value-info-state
       { class foo }
       { interval full-interval }
       { slots
         V{
             f
             T{ value-info-state { class fixnum } { interval T{ interval { from { 42 t } } { to { 42 t } } } } { literal 42 } { literal? t } }
             T{ value-info-state { class fixnum } { interval T{ interval { from { 47 t } } { to { 47 t } } } } { literal 47 } { literal? t } }
         }
       }
     }
} [ [ [ 42 47 <foo> ] final-info ] with-rw first ] unit-test

! ! Accessing slots should not let the object escape
! { f } [ [ 11 22 <foo> [ a>> ] keep ] return-escapes? first ] unit-test
! { f } [ [ 11 22 <foo> [ b>> ] keep ] return-escapes? first ] unit-test
! { f } [ [ T{ foo f 42 47 } [ a>> ] keep ] return-escapes? first ] unit-test
! { f } [ [ T{ foo f 42 47 } [ b>> ] keep ] return-escapes? first ] unit-test
! { f } [ [ T{ foo f 43 47 } [ a>> ] keep ] return-escapes? first ] unit-test
! { f } [ [ T{ foo f 43 47 } [ b>> ] keep ] return-escapes? first ] unit-test

! { V{ 42 47 } } [ [ [ 42 47 <foo> [ a>> ] [ b>> ] bi ] final-literals ] with-rw ] unit-test
! { V{ 42 47 } } [ [ [ 42 47 <foo> foo-slots ] final-literals ] with-rw ] unit-test
! { V{ 43 47 } } [ [ [ 43 47 <foo> foo-slots ] final-literals ] with-rw ] unit-test
! { V{ 42 47 } } [ [ [ T{ foo f 42 47 } [ a>> ] [ b>> ] bi ] final-literals ] with-rw ] unit-test
! { V{ 42 47 } } [ [ [ T{ foo f 42 47 } foo-slots ] final-literals ] with-rw ] unit-test
! { V{ 43 47 } } [ [ [ T{ foo f 43 47 } foo-slots ] final-literals ] with-rw ] unit-test

${ ${ 42 <literal-info> object-info } >vector }
[ [ foo new foo-slots ] final-info ] unit-test

${ ${ 42 <literal-info> f <literal-info> } >vector }
[ [ [ foo new foo-slots ] final-info ] with-rw ] unit-test


! Non-escaping

{ V{ 42 47 } } [ [ [ 42 47 <foo> [ poke drop ] keep foo-slots ] final-literals ] with-rw ] unit-test

! Escaping
{ V{ 42 f } } [ [ [ 42 47 <foo> [ frob ] keep [ a>> ] [ b>> ] bi ] final-literals ] with-rw ] unit-test
{ V{ 42 f } } [ [ [ 42 47 <foo> [ frob ] keep foo-slots ] final-literals ] with-rw ] unit-test

TUPLE: box a ;
C: <box> box
! Nested non-escaping
{ f } [ [ 42 <box> <box> a>> a>> ] final-literals first ] unit-test
{ 42 } [ [ 42 <box> <box> a>> a>> ] rw-literals first ] unit-test

! { f } [ [ 42 <box> dup <box> a>> poke drop ] return-escapes? first ] unit-test

! Nested escape

! ! Boa call
! ! FIXME
! ! { t }
! { f }
! [ [ 42 <box> dup <box> a>> frob ] return-escapes? first ] unit-test

! ! Literals
! ! FIXME
! ! { t }
! { f }
! [ [ T{ box f 42 } dup <box> a>> frob ] return-escapes? first ] unit-test

! ! Set-slot
! ! FIXME
! ! { t }
! { f }
! [ [ box new 42 >>a box new over >>a a>> frob ] return-escapes? first ] unit-test


! TODO: Test with mutated invalid literal
