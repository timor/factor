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


! TODO: class-info
TUPLE: bar { a read-only initial: 42 } b ;


! Basic branch phi

{ V{ T{ interval { from { 11 t } } { to { 33 t } } } full-interval } }
[ [ [ 11 22 foo boa ] [ 33 44 foo boa ] if [ a>> ] [ b>> ] bi ] final-info [ interval>> ] map ] unit-test


! Regular behavior on deref

! Deref info
{ { 42 f } }
[ [ T{ foo f 42 47 } [ a>> ] [ b>> ] bi ]
  final-literals >array ] unit-test

{ { 42 47 } }
[ [ [ T{ foo f 42 47 } [ a>> ] [ b>> ] bi ]
    final-literals >array ] with-rw  ] unit-test

{ { 42 47 } }
[
  [ [ 42 47 foo boa [ a>> ] [ b>> ] bi ]
    final-literals >array ] with-rw ] unit-test

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


! TODO
! Back references

! Initial values
TUPLE: baz { a initial: 42 } { b initial: 47 } ;

! Escaping
: frob ( x -- ) drop ;

{ V{ f f } } [ [ [ baz new [ frob ] keep [ a>> ] [ b>> ] bi ] final-literals ] with-rw ] unit-test


: kill-backref ( info -- info )
    clone f >>backref
    [ clone [ dup [ kill-backref ] when ] map ] change-slots ;

: final-info-no-backref ( quot/word -- seq )
    final-info [ kill-backref ] map ;

! Recursive
! This is really cool, if I may say so myself..
{ T{ baz f 47 42 } } [ 5 [ baz new swap [ [ 1 + ] change-a [ 1 -  ] change-b ] times ] call ] unit-test
{
    T{ value-info-state
       { class baz }
       { interval full-interval }
       { slots
         V{
             f
             T{ value-info-state
                { class integer }
                { interval T{ interval { from { 42 t } } { to { 1/0. t } } } }
                { slot-refs
                  HS{ T{ tuple-slot-ref { object-value 10073 } { slot-num 2 } } T{ tuple-slot-ref { object-value 10139 } { slot-num 2 } } }
                }
              }
             T{ value-info-state
                { class integer }
                { interval T{ interval { from { -1/0. t } } { to { 47 t } } } }
                { slot-refs
                  HS{ T{ tuple-slot-ref { object-value 10089 } { slot-num 3 } } T{ tuple-slot-ref { object-value 10139 } { slot-num 3 } } }
                }
              }
         }
       }
     }
} [ [ [ baz new swap [ [ 1 + ] change-a [ 1 -  ] change-b ] times ] final-info-no-backref first ] with-rw ] unit-test
