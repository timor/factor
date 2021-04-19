USING: accessors compiler.test compiler.tree.propagation.info
compiler.tree.propagation.slots.tests kernel sequences tools.test ;
IN: compiler.tree.propagation.set-slots.tests

TUPLE: bar { a read-only initial: 42 } b ;
SLOT: a

{ V{ f t f } } [ [ bar new 47 >>b ] final-info first slots>> [ slot-ref? ] map ] unit-test
{ V{ f t t } } [ [ [ bar new 47 >>b ] final-info ] with-rw
                 first slots>> [ slot-ref? ] map
               ] unit-test

! Existing behavior
{ V{ 42 f } } [ [ bar new 47 >>b [ a>> ] [ b>> ] bi ] final-literals ] unit-test
{ V{ 42 f } } [ [ [ bar new 47 >>b [ a>> ] [ b>> ] bi ] final-literals ] with-rw ] unit-test
! Invalid write
{ V{ 42 f } } [ [ bar new 66 >>a 47 >>b [ a>> ] [ b>> ] bi ] final-literals ] unit-test

! New behavior
{ V{ f 42 47 } } [ [ [ bar new 47 >>b ] final-info ] with-rw
                   first slots>> [ dup slot-ref? [ literal>> ] when ] map
                 ] unit-test
! Invalid write
{ V{ f 42 47 } } [ [ [ bar new 66 >>a 47 >>b ] final-info ] with-rw
                   first slots>> [ dup slot-ref? [ literal>> ] when ] map
                 ] unit-test

! Basic branches
{ V{ f t f } }
[ [ [ bar new 11 >>b ] [ bar new 22 >>b ] if ] final-info first
  slots>> [ slot-ref? ] map ] unit-test

{ V{ 42 f } }
[ [ [ bar new 11 >>b ] [ bar new 11 >>b ] if [ a>> ] [ b>> ] bi ] final-literals ] unit-test

{ V{ 42 f } }
[ [ [ bar new 11 >>b ] [ bar new 22 >>b ] if [ a>> ] [ b>> ] bi ] final-literals ] unit-test

{ V{ f t t } }
[ [ [ [ 11 22 foo boa ] [ 33 44 foo boa ] if ] final-info ] with-rw first
  slots>> [ slot-ref? ] map ] unit-test

! With rw-propagation
{ V{ 42 f } }
[ [ [ [ bar new 11 >>b ] [ bar new 22 >>b ] if [ a>> ] [ b>> ] bi ] final-literals ] with-rw ] unit-test

! FIXME
! { V{ 42 11 } }
{ V{ 42 f } }
[ [ [ [ bar new 11 >>b ] [ bar new 11 >>b ] if [ a>> ] [ b>> ] bi ] final-literals ] with-rw ] unit-test

! Initial values
TUPLE: baz { a initial: 42 } { b initial: 47 } ;

{ V{ f f } } [ [ baz new [ a>> ] [ b>> ] bi ] final-literals ] unit-test

! Slot info is there
{ V{ f 42 47 } } [ [ [ baz new ] final-info ] with-rw
                   first slots>> [ dup slot-ref? [ literal>> ] when ] map
               ] unit-test

! .. but not dereferenced
! FIXME
{ V{ f f } } [ [ [ baz new [ a>> ] [ b>> ] bi ] final-literals ] with-rw ] unit-test

! Circularity on set-slot?
{ t } [ [ [ circle new dup >>me ] final-info ] with-rw first value-info-state? ] unit-test
