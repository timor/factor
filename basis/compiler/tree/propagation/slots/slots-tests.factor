USING: accessors arrays classes.tuple.private compiler.test compiler.tree
compiler.tree.propagation.copy compiler.tree.propagation.info
compiler.tree.propagation.slots hashtables kernel math math.intervals namespaces
quotations sequences stack-checker.values tools.test vectors words ;
IN: compiler.tree.propagation.slots.tests

: indexize ( seq -- assoc )
    [ swap 2array ] map-index ;

: setup-value-infos ( value-infos -- )
    indexize >hashtable 1array value-infos set
    H{ { 0 0 } { 1 1 } { 2 2 } { 3 3 } } copies set ;

: with-values ( quot -- )
    [ H{ } clone copies set
      H{ } clone 1vector value-infos set
    ] prepose with-scope ; inline

: with-rw ( quot -- )
    propagate-rw-slots swap with-variable-on ; inline

{ t } [
    \ <array> sequence-constructor?
] unit-test

{
    T{ value-info-state
       { class array }
       { interval full-interval }
       { slots
         {
             T{ value-info-state
                { class fixnum }
                { interval
                  T{ interval
                     { from { 7 t } }
                     { to { 7 t } }
                  }
                }
                { literal 7 }
                { literal? t }
             }
         }
       }
    }
} [
    { 7 f } [ <literal-info> ] map setup-value-infos
    { 0 1 } { 2 } \ <array> <#call> dup word>>
    propagate-sequence-constructor first
] unit-test

TUPLE: foo { a read-only } b ;

! Literal slot propagation on read-only-slots
! Tuple literal
{ V{ 42 f } }
[ [ [ T{ foo f 42 47 } [ a>> ] [ b>> ] bi ] final-literals ] with-values ] unit-test

{ { f t f } }
[ [ [ T{ foo f 42 47 } ] final-info ] with-values first slots>> [ slot-ref? ] map ] unit-test

! Existing behavior.  The second value is known because the call to <tuple-info>
! would have set this to f
{ { 42 47 } } [
    [
        42 <literal-info> <value> [ introduce-value ] [ set-value-info ] [ ] tri
        47 <literal-info> <value> [ introduce-value ] [ set-value-info ] [ ] tri
        [ value-info ] bi@ 2array
        foo <tuple-info>
    ] with-values slots>> [ [ literal>> ] [ f ] if* ] map ] unit-test

! New behavior, with references
{ { 42 47 } } [
    [
        42 <literal-info> <value> [ introduce-value ] [ set-value-info ] [ ] tri
        47 <literal-info> <value> [ introduce-value ] [ set-value-info ] [ ] tri
        2array
        foo <tuple-ref-info>
        slots>> [ [ literal>> ] [ f ] if* ] map ] with-values ] unit-test

! Existing behavior
{ { f 42 f } }
[
    { 42 47 } [ <literal-info> ] map
    foo "layout" word-prop <literal-info> suffix
    setup-value-infos
    { 0 1 2 } { 3 } \ <tuple-boa> <#call>
    propagate-<tuple-boa>
    first slots>> [ [ literal>> ] [ f ] if* ] map
] unit-test

! New behavior
{ { f 42 f } }
[
    { 42 47 } [ <literal-info> ] map
    foo "layout" word-prop <literal-info> suffix
    setup-value-infos
    { 0 1 2 } { 3 } \ <tuple-boa> <#call>
    propagate-<tuple-boa>-refs
    first slots>> [ [ literal>> ] [ f ] if* ] map
] unit-test

! Boa constructor
{ V{ 42 f } }
[ [ [ 42 47 foo boa [ a>> ] [ b>> ] bi ] final-literals ] with-values ] unit-test

{ V{ f t f } }
[ [ [ 42 47 foo boa ] final-info ] with-values first slots>> [ slot-ref? ] map ] unit-test

! New
{ V{ f t f } } [ [ foo new ] final-info first slots>> [ slot-ref? ] map ] unit-test
{ V{ f t t } } [ [ [ foo new ] final-info ] with-rw first slots>> [ slot-ref? ] map ] unit-test


! TODO: class-info
TUPLE: bar { a read-only initial: 42 } b ;

{ V{ f t f } }
[ [ [ bar new 47 >>b ] final-info ] with-values first slots>> [ slot-ref? ] map ] unit-test


{ { f t f } } [ [
             T{ foo f 42 47 } <literal-info>
             T{ foo f 69 55 } <literal-info>
             value-info-union slots>> [ slot-ref? ] map
         ] with-values ] unit-test

! Basic branch phi
{ V{ f t f } }
[ [ [ 11 22 foo boa ] [ 33 44 foo boa ] if ] final-info first
  slots>> [ slot-ref? ] map ] unit-test

{ V{ f t t } }
[ [ [ [ 11 22 foo boa ] [ 33 44 foo boa ] if ] final-info ] with-rw first
  slots>> [ slot-ref? ] map ] unit-test

{ V{ T{ interval { from { 11 t } } { to { 33 t } } } full-interval } }
[ [ [ 11 22 foo boa ] [ 33 44 foo boa ] if [ a>> ] [ b>> ] bi ] final-info [ interval>> ] map ] unit-test


! Creating literal now expects slot content on rw slots
! Original
{ { f t f } }
[ T{ foo f 42 47 } tuple-slot-infos [ slot-ref? ] map ] unit-test
! Modified
{ { f t t } }
[ T{ foo f 42 47 } tuple-slot-infos-rw [ slot-ref? ] map ] unit-test

{ { f t f } }
[ T{ foo f 42 47 } <literal-info> slots>> [ slot-ref? ] map ] unit-test

! Regular behavior on deref

! Slot-ref types
{ { f t t } }
[ propagate-rw-slots [ T{ foo f 42 47 } <literal-info> slots>> [ slot-ref? ] map ] with-variable-on ] unit-test

{ { f t t } }
[ propagate-rw-slots [ [ T{ foo f 42 47 } ] final-info first slots>> [ slot-ref? ] map ] with-variable-on ] unit-test
! Deref info
{ { 42 f } }
[ propagate-rw-slots
  [ [ T{ foo f 42 47 } [ a>> ] [ b>> ] bi ]
    final-literals >array ] with-variable-on ] unit-test

{ { 42 f } }
[ propagate-rw-slots
  [ [ 42 47 foo boa [ a>> ] [ b>> ] bi ]
    final-literals >array ] with-variable-on ] unit-test

! Decide to keep rw slots
{
    t
    f
    t
    f
    { f 0 f } foo f
    { f 0 f } foo f
    { f 0 1 } foo f
    { f 0 2 } foo f
} [
    42 <literal-info>
    47 <literal-info>
    object-info 3array setup-value-infos
    ! Old behavior
    42 <literal-info> 47 <literal-info> 2array foo fold-<tuple-boa>? ! t
    42 <literal-info> object-info 2array foo fold-<tuple-boa>? ! f
    ! New behavior, rw-slot deactivated, intermediate implementation ( TBR )
    { f 0 1 } foo fold-<tuple-boa>-values? ! t
    { f 0 2 } foo fold-<tuple-boa>-values? ! f
    ! New behavior, rw-slot-deactivated
    { 0 1 } foo fold-<tuple-boa>-rw? ! { f 0 f } f
    { 0 2 } foo fold-<tuple-boa>-rw? ! { f 0 f } f
    ! New behavior, rw-slot activated
    ! We don't want to fold, but populate slots
    propagate-rw-slots [
        { 0 1 } foo fold-<tuple-boa>-rw? ! { f 0 1 } f
        { 0 2 } foo fold-<tuple-boa>-rw? ! { f 0 2 } f
    ] with-variable-on
] unit-test

! Cross-check actual foldable tuple
TUPLE: ro-tuple { a read-only } { b read-only } ;

! Create slot refs on folding (<literal-info> code path)
{ { f t t } }
[ [ 42 47 ro-tuple boa ] final-info first slots>> [ slot-ref? ] map ] unit-test
{ { f t t } }
[ propagate-rw-slots [ [ 42 47 ro-tuple boa ] final-info first slots>> [ slot-ref? ] map ] with-variable-on ] unit-test


{
    t
    f
    t
    f
    { f 0 1 } ro-tuple t
    { f 0 2 } ro-tuple f
    { f 0 1 } ro-tuple t
    { f 0 2 } ro-tuple f
} [
    42 <literal-info>
    47 <literal-info>
    object-info 3array setup-value-infos
    ! Old behavior
    42 <literal-info> 47 <literal-info> 2array ro-tuple fold-<tuple-boa>? ! t
    42 <literal-info> object-info 2array ro-tuple fold-<tuple-boa>? ! f
    ! New behavior, rw-slot deactivated, intermediate implementation ( TBR )
    { f 0 1 } ro-tuple fold-<tuple-boa>-values? ! t
    { f 0 2 } ro-tuple fold-<tuple-boa>-values? ! f
    ! New behavior, rw-slot-deactivated
    { 0 1 } ro-tuple fold-<tuple-boa>-rw? ! { f 0 1 } t
    { 0 2 } ro-tuple fold-<tuple-boa>-rw? ! { f 0 2 } f
    ! New behavior, rw-slot activated
    ! We don't want to fold, but populate slots
    propagate-rw-slots [
        { 0 1 } ro-tuple fold-<tuple-boa>-rw? ! { f 0 1 } t
        { 0 2 } ro-tuple fold-<tuple-boa>-rw? ! { f 0 2 } f
    ] with-variable-on
] unit-test


{ { f t t } }
[ propagate-rw-slots [ [ 42 47 foo boa ] final-info first slots>> [ slot-ref? ] map >array ] with-variable-on ] unit-test

! Circularity
! TODO: Circularity on set-slot?

! Mutable tuples with circularity should not cause problems
TUPLE: circle me ;

{ { f t } } [ propagate-rw-slots [ circle new dup >>me 1quotation final-info first  ] with-variable-on slots>> [ slot-ref? ] map ] unit-test

! TODO set-slot

{ V{ f t f } } [ [ bar new 47 >>b ] final-info first slots>> [ slot-ref? ] map ] unit-test
{ V{ f t t } } [ [ [ bar new 47 >>b ] final-info ] with-rw
                 first slots>> [ slot-ref? ] map
               ] unit-test

! Existing behavior
{ V{ 42 f } } [ [ bar new 47 >>b [ a>> ] [ b>> ] bi ] final-literals ] unit-test
{ V{ 42 f } } [ [ [ bar new 47 >>b [ a>> ] [ b>> ] bi ] final-literals ] with-rw ] unit-test

! New behavior
{ V{ f 42 47 } } [ [ [ bar new 47 >>b ] final-info ] with-rw
                first slots>> [ dup slot-ref? [ literal>> ] when ] map
              ] unit-test
