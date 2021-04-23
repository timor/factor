USING: accessors compiler.test
compiler.tree.propagation.info kernel math sequences tools.test ;
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
! Invalid write
{ V{ 42 f } } [ [ bar new 66 >>a 47 >>b [ a>> ] [ b>> ] bi ] final-literals ] unit-test


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

! Initial values
TUPLE: baz { a initial: 42 } { b initial: 47 } ;

{ V{ f f } } [ [ baz new [ a>> ] [ b>> ] bi ] final-literals ] unit-test

{ V{ 42 47 } } [ [ [ baz new [ a>> ] [ b>> ] bi ] final-literals ] with-rw ] unit-test

TUPLE: circle me ;
! Circularity on set-slot?

! ! FIXME
! { t } [ [ [ circle new dup >>me ] final-info ] with-rw first value-info-state? ] unit-test

! Nested updates
TUPLE: box a ;
C: <box> box
! Nested non-escaping
{ 43 } [ 42 <box> [ <box> a>> [ 1 + ] change-a drop ] keep a>> ] unit-test
{ f } [ [ 42 <box> [ <box> a>> [ 1 + ] change-a drop ] keep a>> ] final-literals first ] unit-test
! FIXME
! { 43 }
{ 42 }
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
