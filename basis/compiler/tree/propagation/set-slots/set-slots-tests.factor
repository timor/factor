USING: accessors compiler.test compiler.tree.propagation.escaping.tests
compiler.tree.propagation.info kernel math sequences tools.test ;
IN: compiler.tree.propagation.set-slots.tests

TUPLE: foo { a read-only } b ;
TUPLE: bar { a read-only initial: 42 } b ;
SLOT: a


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

{ t } [ [ [ circle new dup >>me ] final-info ] with-rw first value-info-state? ] unit-test

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


! Storing mutable in two different slots, mutate, access changed slots
{ 43 43 43 } [ 42 <box> [ <box> ] [ <box> ] [  ] tri [ 1 + ] change-a a>> [ [ a>> a>> ] bi@ ] dip ] unit-test
{ V{ 43 43 43 } } [ [ 42 <box> [ <box> ] [ <box> ] [  ] tri [ 1 + ] change-a a>> [ [ a>> a>> ] bi@ ] dip ] rw-literals ] unit-test
