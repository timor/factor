USING: accessors arrays compiler.test compiler.tree.propagation.info generalizations
kernel kernel.private literals math math.intervals sequences tools.test ;
IN: compiler.tree.propagation.set-slots.tests

TUPLE: foo { a read-only } b ;
TUPLE: bar { a read-only initial: 42 } b ;
SLOT: a

: rw-literals ( quot/word -- seq )
    [ final-literals ] with-rw ;


! Existing behavior
{ V{ 42 f } } [ [ bar new 47 >>b [ a>> ] [ b>> ] bi ] final-literals ] unit-test
! New behavior
{ V{ 42 47 } } [ [ [ bar new 47 >>b [ a>> ] [ b>> ] bi ] final-literals ] with-rw ] unit-test
! ! Invalid write
! { V{ f f } } [ [ bar new 66 >>a 47 >>b [ a>> ] [ b>> ] bi ] final-literals ] unit-test


! Basic branches

{ V{ 42 f } }
[ [ [ bar new 11 >>b ] [ bar new 11 >>b ] if [ a>> ] [ b>> ] bi ] final-literals ] unit-test

{ V{ 42 f } }
[ [ [ bar new 11 >>b ] [ bar new 22 >>b ] if [ a>> ] [ b>> ] bi ] final-literals ] unit-test

! With rw-propagation
{ V{ 42 f } }
[ [ [ [ bar new 11 >>b ] [ bar new 22 >>b ] if [ a>> ] [ b>> ] bi ] final-literals ] with-rw ] unit-test

{ V{ 42 11 } }
[ [ [ [ bar new 11 >>b ] [ bar new 11 >>b ] if [ a>> ] [ b>> ] bi ] final-literals ] with-rw ] unit-test

! Commenting out, too specific right now.
! ! Returning tuples
! {
!     T{ value-info-state
!         { class bar }
!         { interval full-interval }
!         { slots
!             {
!                 f
!                 T{ lazy-info
!                     { values { 10059 10103 } }
!                     { ro? t }
!                     { cached
!                         T{ value-info-state
!                             { class fixnum }
!                             { interval T{ interval { from { 42 t } } { to { 42 t } } } }
!                             { literal 42 }
!                             { literal? t }
!                             { origin HS{ T{ literal-allocation { literal 42 } } } }
!                         }
!                     }
!                 }
!                 T{ lazy-info
!                     { values { 10060 10104 } }
!                     { cached
!                         T{ value-info-state
!                             { class fixnum }
!                             { interval T{ interval { from { 11 t } } { to { 33 t } } } }
!                             { origin HS{ T{ literal-allocation { literal 11 } } T{ literal-allocation { literal 33 } } } }
!                         }
!                     }
!                 }
!             }
!         }
!         { origin HS{ local-allocation } }
!     }
! }
! [ [ [ [ bar new 11 >>b ] [ bar new 33 >>b ] if ] final-value-info first ] with-rw ] unit-test

! Initial values
TUPLE: baz { a initial: 42 } { b initial: 47 } ;
C: <baz> baz

{ V{ f f } } [ [ baz new [ a>> ] [ b>> ] bi ] final-literals ] unit-test

{ V{ 42 47 } } [ [ [ baz new [ a>> ] [ b>> ] bi ] final-literals ] with-rw ] unit-test

TUPLE: circle me ;
! Circularity on set-slot?

{ t } [ [ [ circle new dup >>me ] final-info ] with-rw first value-info-state? ] unit-test

! Nested updates
TUPLE: box a ;
C: <box> box
! Nested non-escaping
{ 43 } [ 42 <box> [ <box> a>> [ 1 + ] change-a drop ] keep a>> ] unit-test
{ f } [ [ 42 <box> [ <box> a>> [ 1 + ] change-a drop ] keep a>> ] final-literals first ] unit-test
{ 43 }
[ [ 42 <box> [ <box> a>> [ 1 + ] change-a drop ] keep a>> ] rw-literals first ] unit-test

! Helper for checking that slot-nums are handled correctly
TUPLE: box2 b a ;
: <box2> ( value -- obj ) box2 new swap >>a ; inline

! Storing mutable in two different slots, mutate, access changed slots
! Change the slot of the bottom-of-stack reference, access the others
{ 43 43 43 } [ 42 <box> [ <box2> ] [ <box2> ] [  ] tri [ 1 + ] change-a a>> [ [ a>> a>> ] bi@ ] dip ] unit-test
{ V{ 43 43 43 } } [ [ 42 <box> [ <box2> ] [ <box2> ] [  ] tri [ 1 + ] change-a a>> [ [ a>> a>> ] bi@ ] dip ] rw-literals ] unit-test
! IR Debug values [ 42 T1 [ T2 ] [ T3 ] ... ]
! 10001: 42
! 10004: T1
! 10016: T2
! 10025: T3
! At set-slot call site: 10042: 43, 10043 -> 10004, 10062: 2

! Change the slot of the bottom-of-stack reference, access all of them through two levels of nesting
{ 43 43 43 } [ 42 <box> [ <box> ] [ <box> ] [ <box> ] tri pick a>> [ 1 + ] change-a drop [ a>> a>> ] tri@ ] unit-test
{ V{ 43 43 43 } } [ [ 42 <box> [ <box> ] [ <box> ] [ <box> ] tri pick a>> [ 1 + ] change-a drop [ a>> a>> ] tri@ ] rw-literals ] unit-test

! Same but with top reference
{ 43 43 43 } [ 42 <box> [ <box> ] [ <box> ] [ <box> ] tri dup a>> [ 1 + ] change-a drop [ a>> a>> ] tri@ ] unit-test
{ V{ 43 43 43 } } [ [ 42 <box> [ <box> ] [ <box> ] [ <box> ] tri dup a>> [ 1 + ] change-a drop [ a>> a>> ] tri@ ] rw-literals ] unit-test

! Mixed level of nesting, changing bottom-of stack reference
{ 43 43 43 } [ 42 <box> dup [ <box> ] [ <box> <box> ] bi pick [ 1 + ] change-a drop [ a>> ] [ a>> a>> ] [ a>> a>> a>> ] tri* ] unit-test

! Same, but change top of stack reference
{ 43 43 43 } [ 42 <box> dup [ <box> ] [ <box> <box> ] bi dup a>> a>> [ 1 + ] change-a drop [ a>> ] [ a>> a>> ] [ a>> a>> a>> ] tri* ] unit-test

! Same, but change middle reference
{ 43 43 43 } [ 42 <box> dup [ <box> ] [ <box> <box> ] bi over a>> [ 1 + ] change-a drop [ a>> ] [ a>> a>> ] [ a>> a>> a>> ] tri* ] unit-test

TUPLE: inner a ;
C: <inner> inner
! Transfer with slot retrieval
{ T{ inner f 43 } T{ box f T{ inner f 43 } } T{ inner f 43 } T{ box f T{ inner f 43 } } T{ inner f 43 } }
[ 42 <inner> box new over >>a dup a>> box new over >>a dup a>> [ 1 + ] change-a ] unit-test

{ V{ 43 f 43 f 43 } } [ [ [ 42 <inner> box new over >>a dup a>> box new over >>a dup a>> [ 1 + ] change-a [ a>> ] 5 napply ] final-literals ] with-rw ] unit-test

! Non-unique destructive access
{
    T{ baz f 42 22 }
    T{ baz f 33 44 }
 }
[ t [ 11 22 <baz> 33 44 <baz> [ rot [ drop 42 >>a drop ] [ nip 42 >>a drop ] if ] 2keep ] call ] unit-test

{
    T{ baz f 11 22 }
    T{ baz f 42 44 }
}
[ f [ 11 22 <baz> 33 44 <baz> [ rot [ drop 42 >>a drop ] [ nip 42 >>a drop ] if ] 2keep ] call ] unit-test


{
    { T{ interval { from { 11 t } } { to { 42 t } } } T{ interval { from { 22 t } } { to { 22 t } } } }
    { T{ interval { from { 33 t } } { to { 42 t } } } T{ interval { from { 44 t } } { to { 44 t } } } }
}
[ [ [ 11 22 <baz> 33 44 <baz> [ rot [ drop 42 >>a drop ] [ nip 42 >>a drop ] if ] 2keep ]
    final-info first2 [ slots>> rest [ interval>> ] map ] bi@ ] with-rw ] unit-test

{
    { T{ interval { from { 11 t } } { to { 77 t } } } T{ interval { from { 22 t } } { to { 80 t } } } }
    { T{ interval { from { 11 t } } { to { 77 t } } } T{ interval { from { 22 t } } { to { 80 t } } } }
}
[ [ [ 11 22 <baz> 33 44 <baz> [ rot [ swap ] when 77 >>a 80 >>b drop ] 2keep ]
    final-info first2 [ slots>> rest [ interval>> ] map ] bi@ ] with-rw ] unit-test

! Resize-array

! Lenghts
: final-rw-lengths ( quot/word -- infos )
    [ final-info [ slots>> ?first ] map ] with-rw ;

{ 0 } [ { 1 2 3 } [ { array } declare 0 swap resize-array length ] call ] unit-test
{ 0 } [ [ { } ] final-rw-lengths first literal>> ] unit-test
! { f } [ [ { } 33 suffix ] final-literals first ] unit-test
! { 1 } [ [ [ { } 34 suffix ] final-info ] with-rw ] unit-test
! { 1 } [ [ { } 34 suffix ] final-rw-lengths first literal>> ] unit-test
! { 1 } [ [ { } 35 suffix ] final-rw-lengths first literal>> ] unit-test
{ 42 } [ [ { } 42 swap resize-array ] final-rw-lengths first literal>> ] unit-test
{ 0 } [ [ { 1 2 3 } 0 swap resize-array ] final-rw-lengths first literal>> ] unit-test
{ { } } [ { 1 2 3 } [ { array } declare 0 swap resize-array ] call ] unit-test
{ 0 } [ [ { array } declare 0 swap resize-array ] final-rw-lengths first literal>> ] unit-test
{ 42 } [ [ { array } declare 42 swap resize-array ] final-rw-lengths first literal>> ] unit-test
{ 3 42 } [ { 1 2 3 } [ { array } declare 42 over resize-array ] call [ length ] bi@ ] unit-test
{ f 42 } [ [ { array } declare 42 over resize-array ] final-rw-lengths first2 literal>> ] unit-test
{ 42 } [ [ { array } declare 42 swap resize-array ] final-rw-lengths first literal>> ] unit-test
! Not inventing slots based on declaration only
{ f } [ [ { array } declare ] final-rw-lengths first ] unit-test
${ 0 42 [a,b] } [ [ { } swap [ 42 swap resize-array ] when ] final-rw-lengths first interval>> ] unit-test
${ 0 42 [a,b] } [ [ { } clone swap [ 42 swap resize-array ] when ] final-rw-lengths first interval>> ] unit-test
${ 0 42 [a,b] } [ [ { } clone swap [ 42 clone swap resize-array ] when ] final-rw-lengths first interval>> ] unit-test
${ 0 42 [a,b] } [ [ { } swap [ 42 clone swap resize-array ] when ] final-rw-lengths first interval>> ] unit-test
{ 0 0 } [ f [ { } dup rot [ 42 swap resize-array ] when ] call [ length ] bi@ ] unit-test
{ 0 42 } [ t [ { } dup rot [ 42 swap resize-array ] when ] call [ length ] bi@ ] unit-test
${ 0 0 42 [a,b] } [ [ { } dup rot [ 42 swap resize-array ] when ] final-rw-lengths first2 [ literal>> ] [ interval>> ] bi* ] unit-test
${ 0 0 42 [a,b] } [ [ { } dup clone rot [ 42 swap resize-array ] when ] final-rw-lengths first2 [ literal>> ] [ interval>> ] bi* ] unit-test

{ 0 0 } [ t [ 42 0 <array> dup rot [ 0 swap resize-array ] when ] call [ length ] bi@ ] unit-test
{ 42 42 } [ f [ 42 0 <array> dup rot [ 0 swap resize-array ] when ] call [ length ] bi@ ] unit-test
${ 0 42 [a,b] 0 42 [a,b] } [ [ 42 0 <array> dup rot [ 0 swap resize-array ] when ] final-rw-lengths first2 [ interval>> ] [ interval>> ] bi* ] unit-test
${ 0 42 [a,b] 0 42 [a,b] } [ [ 42 0 <array> dup rot [ 0 swap resize-array ] when ] final-rw-lengths first2 [ interval>> ] [ interval>> ] bi* ] unit-test

{ 42 0 } [ t [ 42 0 <array> dup clone rot [ 0 swap resize-array ] when ] call [ length ] bi@ ] unit-test
{ 42 42 } [ f [ 42 0 <array> dup clone rot [ 0 swap resize-array ] when ] call [ length ] bi@ ] unit-test
${ 42 0 42 [a,b] } [ [ 42 0 <array> dup clone rot [ 0 swap resize-array ] when ] final-rw-lengths first2 [ literal>> ] [ interval>> ] bi* ] unit-test

! Operating on declarations only doesn't affect input
{ 13 13 } [ 42 0 <array> [ { array } declare 13 over resize-array ] call [ length ] bi@ ] unit-test
${ f 13 }
[ [ { array } declare 13 over resize-array ] final-rw-lengths first2 literal>> ] unit-test
{ 13 42 } [ 13 0 <array> [ { array } declare 42 over resize-array ] call [ length ] bi@ ] unit-test

! Resize-array on a nested array

{ 42 13 } [ 13 0 <array> [ <box> a>> 42 swap resize-array ] keep [ length ] bi@ ] unit-test
{ 42 13 } [ [ 13 0 <array> [ <box> a>> 42 swap resize-array ] keep ] final-rw-lengths first2 [ literal>> ] bi@ ] unit-test
{ 13 13 } [ 42 0 <array> [ <box> a>> 13 swap resize-array ] keep [ length ] bi@ ] unit-test
{ 13 13 } [ [ 42 0 <array> [ <box> a>> 13 swap resize-array ] keep ] final-rw-lengths first2 [ literal>> ] bi@ ] unit-test

{ [ { 1 2 3 } 3 swap resize-array ] } [ [ { 1 2 3 } 3 swap resize-array ] optimize-quot ] unit-test
{ [ { 1 2 3 } ] } [ [ [ { 1 2 3 } 3 swap resize-array ] optimize-quot ] with-rw ] unit-test

{ [ { 1 2 3 } 5 swap resize-array ] } [ [ [ { 1 2 3 } 5 swap resize-array ] optimize-quot ] with-rw ] unit-test

! We de-literalize on shrinkage, even when essentially copying input info
{ [ { 1 2 3 } 0 swap resize-array ] } [  [ { 1 2 3 } 0 swap resize-array ] optimize-quot ] unit-test
{ [ { 1 2 3 } 0 swap resize-array ] } [ [ [ { 1 2 3 } 0 swap resize-array ] optimize-quot ] with-rw ] unit-test

! TODO element access/locals
