USING: accessors arrays classes compiler.test compiler.tree.builder
compiler.tree.debugger compiler.tree.optimizer
compiler.tree.propagation.escaping compiler.tree.propagation.info
compiler.tree.propagation.origins generalizations kernel kernel.private math
math.intervals namespaces namespaces.private sequences tools.test ;
IN: compiler.tree.propagation.escaping.tests
FROM: compiler.tree.propagation.escaping => value-escapes ;

! Escaping
TUPLE: box a ;
C: <box> box

TUPLE: foo { a read-only initial: 42 } b ;
C: <foo> foo


: frob-box ( x -- ) [ 1 + ] change-a drop ;
: frob-foo ( x -- ) [ 1 + ] change-b drop ;
: poke ( x -- x ) ; flushable

: rw-literals ( quot/word -- seq )
    [ final-literals ] with-rw ;

: return-escapes? ( quot/word -- seq )
    ! [ propagated-tree last in-d>> [ resolve-copy value-escapes? ] map ] with-rw ;
    [ final-value-info [ value-info-escapes? ] map escaping-values get allocations get
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
{ t } [ [ foldable-magic ] return-escapes? first ] unit-test

{ f t } [ [ dup foldable-magic ] return-escapes? first2 ] unit-test


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
         }
        T{ value-info-state { class object } { interval full-interval } }
    }
}
[ [ [ foo new foo-slots ] final-info ] with-values ] unit-test

! Non-escaping

{ V{ 42 47 } } [ [ [ 42 47 <foo> [ poke drop ] keep foo-slots ] final-literals ] with-rw ] unit-test

TUPLE: inner a ;
C: <inner> inner
{ V{ f f f f f } } [ [ [ 42 <inner> box new over >>a dup a>> box new over >>a dup a>> [ frob-box ] keep [ a>> ] 5 napply ] final-literals ] with-rw ] unit-test


{ T{ foo f 42 48 } } [ 42 47 <foo> [ frob-foo ] keep ] unit-test
{ 42 48 } [ 42 47 <foo> [ frob-foo ] keep [ a>> ] [ b>> ] bi ] unit-test
{ V{ 42 f } } [ [ [ 42 47 <foo> [ frob-foo ] keep [ a>> ] [ b>> ] bi ] final-literals ] with-rw ] unit-test
{ V{ 42 f } } [ [ [ 42 47 <foo> [ frob-foo ] keep foo-slots ] final-literals ] with-rw ] unit-test

! Nested non-escaping
{ f } [ [ 42 <box> <box> a>> a>> ] final-literals first ] unit-test
{ 42 } [ [ 42 <box> <box> a>> a>> ] rw-literals first ] unit-test

{ f } [ [ 42 <box> dup <box> a>> poke drop ] return-escapes? first ] unit-test

! Nested escape

: mangle ( x -- ) dup a>> 999 swap a<< 888 swap a<< ;
: mangle-inner ( x -- ) dup a>> 999 swap a<< T{ inner f 777 } swap a<< ;
! Parent escapes, nested structure is changed
{ T{ box f 888 } T{ inner f 999 } } [ 42 <inner> [ <box> dup mangle ] [ ] bi ] unit-test

! Test invalidating shared slot, setting afterwards, may not propagate over!
{ T{ inner f 999 } T{ box f 888 } } [ 42 <inner> dup <box> [ mangle ] keep ] unit-test
{ T{ inner f 999 } 888 } [ 42 <inner> dup <box> [ mangle ] [ a>> ] bi ] unit-test

{ T{ inner f 999 } T{ inner f 999 } } [ 42 <inner> dup [ <box> mangle ] keep ] unit-test
{ T{ inner f 999 } 999 } [ 42 <inner> dup [ <box> mangle ] [ a>> ] bi ] unit-test

{ T{ inner f 43 } T{ inner f 43 } } [ 42 <inner> dup [ <box> mangle ] keep 43 >>a ] unit-test
{ T{ inner f 999 } T{ inner f 777 } } [ 42 <inner> dup <box> [ mangle-inner ] keep a>> ] unit-test
{ f } [ 42 <inner> dup <box> [ mangle-inner ] keep a>> = ] unit-test
{ f } [ 42 <inner> dup <box> [ mangle-inner ] keep a>> eq? ] unit-test

{ t } [ 42 <inner> dup <box> a>> eq? ] unit-test
! FIXME: Prove identity through slots
! { t }
{ f } [ [ 42 <inner> dup <box> a>> eq? ] rw-literals first ] unit-test

{ f } [ 42 <inner> dup <box> [ mangle-inner ] keep a>> = ] unit-test
{ f } [ [ 42 <inner> dup <box> [ mangle-inner ] keep a>> = ] rw-literals first ] unit-test

! TODO: clone

{ t t } [ [ 42 <inner> [ <box> dup mangle ] [ ] bi ] return-escapes? first2 ] unit-test
{ f } [ [ 42 <inner> [ <box> mangle ] [ ] bi a>> ] rw-literals first ] unit-test

! Boa call
{ T{ box f 43 } } [ 42 <box> dup <box> a>> frob-box ] unit-test
{ 43  } [ 42 <box> dup <box> a>> frob-box a>> ] unit-test
{ t }
[ [ 42 <box> dup <box> a>> frob-box ] return-escapes? first ] unit-test

! Literals
{ T{ box f 43 } } [ T{ box f 42 } dup <box> a>> frob-box ] unit-test
{ 43 } [ T{ box f 42 } dup <box> a>> frob-box a>> ] unit-test


! Must be de-literalized
{ f }
[ [ T{ box f 42 } dup <box> a>> frob-box a>> ] rw-literals first ] unit-test
{
    T{ value-info-state
       { class box }
       { interval empty-interval }
       { literal T{ box { a 42 } } }
       { literal? t }
       { slots
         {
             f
             T{ lazy-info
                { values { 10009 } }
                { cached
                  T{ value-info-state { class fixnum } { interval T{ interval { from { 42 t } } { to { 42 t } } } } { literal 42 } { literal? t } }
                }
              }
         }
       }
       { origin HS{ literal-allocation } }
     }
}
[ [ [ T{ box f 42 } dup <box> a>> frob-box ] final-value-info first ] with-rw ] unit-test

{ t }
[ [ T{ box f 42 } dup <box> a>> frob-box ] return-escapes? first ] unit-test

! Nested literal, pulling out the inner one and modifying it
{ T{ box f T{ inner f 43 } }
  T{ inner f 43 }
} [ T{ box f T{ inner f 42 } } dup a>> 43 >>a ] unit-test

{ 43 43 } [ T{ box f T{ inner f 42 } } dup a>> [ frob-box ] keep [ a>> a>> ] [ a>> ] bi* ] unit-test
{ f f } [ [ T{ box f T{ inner f 42 } } dup a>> [ frob-box ] keep [ a>> a>> ] [ a>> ] bi* ] rw-literals first2 ] unit-test
{ t t } [ [ T{ box f T{ inner f 42 } } dup a>> [ frob-box ] keep ] return-escapes? first2 ] unit-test

{ T{ box f 888 } 888 } [ T{ box f T{ inner f 42 } } [ mangle ] keep dup a>> ] unit-test
{ t t } [ [ T{ box f T{ inner f 42 } } [ mangle ] keep dup a>> ] return-escapes? first2 ] unit-test
! NOTE: We get a literal in the info, but we won't dereference it on slot calls.
{ T{ box f T{ inner f 42 } } f }
[ [ T{ box f T{ inner f 42 } } [ mangle ] keep dup a>> ] rw-literals first2 ] unit-test

! Verify same behavior with nesting in read-only slots
TUPLE: ro-box { a read-only } ;
C: <ro-box> ro-box

! Nested non-literals, pulling out inner one and modifying it

{ T{ ro-box f T{ inner f 43 } }
  T{ inner f 43 }
} [ 42 <inner> <ro-box> dup a>> 43 >>a ] unit-test
{ 43 43 } [ 42 <inner> <ro-box> dup a>> [ frob-box ] keep [ a>> a>> ] [ a>> ] bi* ] unit-test
{ f f } [ [ 42 <inner> <ro-box> dup a>> [ frob-box ] keep [ a>> a>> ] [ a>> ] bi* ]
          rw-literals first2 ] unit-test
{ t t } [ [ 42 <inner> <ro-box> dup a>> [ frob-box ] keep [ a>> a>> ] [ a>> ] bi* ]
          return-escapes? first2
        ] unit-test

! Nested literal, pulling out the inner one and modifying it
{ T{ ro-box f T{ inner f 43 } }
  T{ inner f 43 }
} [ T{ ro-box f T{ inner f 42 } } dup a>> 43 >>a ] unit-test

{ 43 43 } [ T{ ro-box f T{ inner f 42 } } dup a>> [ frob-box ] keep [ a>> a>> ] [ a>> ] bi* ] unit-test
{ f f } [ [ T{ ro-box f T{ inner f 42 } } dup a>> [ frob-box ] keep [ a>> a>> ] [ a>> ] bi* ] rw-literals first2 ] unit-test
{ t t } [ [ T{ ro-box f T{ inner f 42 } } dup a>> [ frob-box ] keep ] return-escapes? first2 ] unit-test

{ t } [ [ foo new dup ro-box boa a>> frob-box ] return-escapes? first ] unit-test

! Set-slot

{ T{ box f 43 } } [ box new 42 >>a box new over >>a a>> frob-box ] unit-test
{ 43 } [ box new 42 >>a box new over >>a a>> frob-box a>> ] unit-test
{ f } [ [ [ box new 42 >>a box new over >>a a>> frob-box a>> ] final-literals first ] with-rw ] unit-test
{ t } [ box new 42 >>a box new over >>a a>> [ frob-box ] keep eq? ] unit-test
{ t t } [ [ box new 42 >>a box new over >>a a>> [ frob-box ] keep ] return-escapes? first2 ] unit-test
{ t } [ [ box new 42 >>a box new over >>a a>> frob-box ] return-escapes? first ] unit-test


! Store in two boxes, keep original and frob it, check if slots in boxes escape correctly
{ 23 23 } [ foo new 22 >>b [ <box> ] [ <box> ] [ ] tri frob-foo [ a>> b>> ] bi@ ] unit-test

{ V{ 22 22 } }
[ [ foo new 22 >>b [ <box> ] [ <box> ] [ ] tri drop [ a>> b>> ] bi@ ] rw-literals ] unit-test

{ V{ f f } }
[ [ foo new 22 >>b [ <box> ] [ <box> ] [ ] tri frob-foo [ a>> b>> ] bi@ ] rw-literals ] unit-test

! Ro-slots not affected
{ 42 42 } [ foo new 22 >>b [ <box> ] [ <box> ] [ ] tri frob-foo [ a>> a>> ] bi@ ] unit-test

! TODO: Test with mutated invalid literal
! TODO: circular escapes, nested circular escapes

! Crosscheck failure from acll-effect-tests
: optimized-quot ( quot -- quot' )
    build-tree optimize-tree nodes>quot ;

{ [ 3 ] } [ [ [ 1 2 \ + execute( a b -- c ) ] optimized-quot ] with-rw ] unit-test

: frob-array ( array -- ) drop ;
! Escaping in arrays
{ t } [ [ foo new dup 1array frob-array ] return-escapes? first ] unit-test
{ t } [ [ foo new 1 f <array> 2dup 0 swap set-nth frob-array ] return-escapes? first ] unit-test
{ t } [ [ { array } declare foo new swap 2dup 0 swap set-nth frob-array ] return-escapes? first ] unit-test

! Strong updates in single-element arrays
{ f t } [ [| |
         foo new :> f1
         foo new :> f2
         f1 1array :> arr
         f2 0 arr set-nth
         arr frob-array
         f1 f2
        ] return-escapes? first2 ] unit-test

! Weak updates in single-element arrays
{ t t } [ [| |
           foo new :> f1
           foo new :> f2
           f1 f 2array :> arr
           f2 0 arr set-nth
           arr frob-array
           f1 f2
          ] return-escapes? first2 ] unit-test

! Escaping after allocating and retrieving from array slots
{ t } [ [ foo new dup 11 2array first frob-array ] return-escapes? first ] unit-test
{ t } [ [ foo new dup 11 swap 2array first frob-array ] return-escapes? first ] unit-test
{ t } [ [ foo new dup 11 2array second frob-array ] return-escapes? first ] unit-test
{ t } [ [ foo new dup 11 swap 2array second frob-array ] return-escapes? first ] unit-test

! Inner slots of magical call results unknown
{ t } [ [ global ] return-escapes? first ] unit-test
{ global-box } [ [ "include" global box-at ] final-literals first class-of ] unit-test
{ global-box } [ [ [ "include" global box-at ] final-literals first ] with-rw class-of ] unit-test
{ t } [ [ "include" get-global ] return-escapes? first ] unit-test
{ f } [ [ "include" get-global ] rw-literals first ] unit-test