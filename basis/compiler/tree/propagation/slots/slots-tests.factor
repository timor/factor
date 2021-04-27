USING: accessors arrays classes.struct classes.tuple.private compiler.test
compiler.tree compiler.tree.propagation.copy compiler.tree.propagation.info
compiler.tree.propagation.slots hashtables kernel kernel.private math
math.intervals namespaces sequences stack-checker.values tools.test vectors
words ;
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
C: <foo> foo

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

! Declared
{ 43 48 } [ 43 48 <foo> { foo } declare [ a>> ] [ b>> ] bi ] unit-test

{ 43 f } [ [ 43 48 <foo> [ a>> ] [ b>> ] bi ] final-literals first2 ] unit-test
{ 43 f } [ [ 43 48 <foo> { foo } declare [ a>> ] [ b>> ] bi ] final-literals first2 ] unit-test

{ 43 48 } [ [ [ 43 48 <foo> [ a>> ] [ b>> ] bi ] final-literals first2 ] with-rw ] unit-test
{ 43 48 } [  43 48 <foo> { foo } declare [ a>> ] [ b>> ] bi ] unit-test
{ 43 48 } [ [ [ 43 48 <foo> { foo } declare [ a>> ] [ b>> ] bi ] final-literals first2 ] with-rw ] unit-test

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


! Recursive
! This is really cool, if I may say so myself..
{ T{ baz f 47 42 } } [ 5 [ baz new swap [ [ 1 + ] change-a [ 1 -  ] change-b ] times ] call ] unit-test
{
    T{ value-info-state
       { class baz }
       { interval full-interval }
       { slots
         {
             f
             T{ value-info-state
                { class integer }
                { interval T{ interval { from { 42 t } } { to { 1/0. t } } } }
                { origin HS{ T{ literal-allocation { literal 42 } } local-allocation } }
              }
             T{ value-info-state
                { class integer }
                { interval T{ interval { from { -1/0. t } } { to { 47 t } } } }
                { origin HS{ local-allocation T{ literal-allocation { literal 47 } } } }
              }
         }
       }
       { origin HS{ local-allocation } }
     }
} [ [ [ baz new swap [ [ 1 + ] change-a [ 1 -  ] change-b ] times ] final-info first ] with-rw ] unit-test

TUPLE: box a ;
C: <box> box

! Keeping a reference outside the loop
{
    T{ box { a T{ baz { a 52 } { b 37 } } } }
    T{ baz { a 52 } { b 37 } }
}
[ 10 [ baz new [ <box> ] keep rot [ [ 1 + ] change-a [ 1 - ] change-b ] times ] call ] unit-test

{
V{
    T{ value-info-state
        { class box }
        { interval full-interval }
        { slots
            {
                f
                T{ value-info-state
                    { class baz }
                    { interval full-interval }
                    { slots
                        {
                            f
                            T{ value-info-state
                                { class integer }
                                { interval T{ interval { from { 42 t } } { to { 1/0. t } } } }
                                { origin
                                    HS{ local-allocation T{ literal-allocation { literal 42 } } }
                                }
                            }
                            T{ value-info-state
                                { class integer }
                                { interval T{ interval { from { -1/0. t } } { to { 47 t } } } }
                                { origin
                                    HS{ local-allocation T{ literal-allocation { literal 47 } } }
                                }
                            }
                        }
                    }
                    { origin HS{ local-allocation } }
                }
            }
        }
        { origin HS{ local-allocation } }
    }
    T{ value-info-state
        { class baz }
        { interval full-interval }
        { slots
            {
                f
                T{ value-info-state
                    { class integer }
                    { interval T{ interval { from { 42 t } } { to { 1/0. t } } } }
                    { origin HS{ local-allocation T{ literal-allocation { literal 42 } } } }
                }
                T{ value-info-state
                    { class integer }
                    { interval T{ interval { from { -1/0. t } } { to { 47 t } } } }
                    { origin HS{ local-allocation T{ literal-allocation { literal 47 } } } }
                }
            }
        }
        { origin HS{ local-allocation } }
    }
}
} [ [ [ baz new [ <box> ] keep rot [ [ 1 + ] change-a [ 1 - ] change-b ] times ] final-info ] with-rw ] unit-test


! Modifying the slot after the loop

{
    T{ box { a T{ baz { a 30 } { b 37 } } } }
    T{ baz { a 30 } { b 37 } }
}
[ 10 [ baz new [ <box> ] keep rot [ [ 1 + ] change-a [ 1 - ] change-b ] times [ 22 - ] change-a ] call ] unit-test

{
V{
    T{ value-info-state
        { class box }
        { interval full-interval }
        { slots
            {
                f
                T{ value-info-state
                    { class baz }
                    { interval full-interval }
                    { slots
                        {
                            f
                            T{ value-info-state
                                { class integer }
                                { interval T{ interval { from { 20 t } } { to { 1/0. t } } } }
                                { origin
                                    HS{
                                        T{ literal-allocation { literal 42 } }
                                        local-allocation
                                    }
                                }
                            }
                            T{ value-info-state
                                { class integer }
                                { interval T{ interval { from { -1/0. t } } { to { 47 t } } } }
                                { origin
                                    HS{ local-allocation T{ literal-allocation { literal 47 } } }
                                }
                            }
                        }
                    }
                    { origin HS{ local-allocation } }
                }
            }
        }
        { origin HS{ local-allocation } }
    }
    T{ value-info-state
        { class baz }
        { interval full-interval }
        { slots
            {
                f
                T{ value-info-state
                    { class integer }
                    { interval T{ interval { from { 20 t } } { to { 1/0. t } } } }
                    { origin
                        HS{
                            local-allocation
                            T{ literal-allocation { literal 42 } }
                        }
                    }
                }
                T{ value-info-state
                    { class integer }
                    { interval T{ interval { from { -1/0. t } } { to { 47 t } } } }
                    { origin HS{ local-allocation T{ literal-allocation { literal 47 } } } }
                }
            }
        }
        { origin HS{ local-allocation } }
    }
}

}
[ [ [ baz new [ <box> ] keep rot [ [ 1 + ] change-a [ 1 - ] change-b ] times [ 22 - ] change-a ] final-info ] with-rw ] unit-test

! TODO: combine with branches

! Recursive infinite compile loop checks

{ vector } [ [ [ { vector } declare [ 1 + ] map ] final-classes first ] with-rw ] unit-test
{ vector } [ [ [ V{  } clone [ 1 + ] map ] final-classes first ] with-rw ] unit-test

! ! Crosscheck recursive problems

! Appending to a vector
{ V{ 42 42 42 } } [ 3 [ V{ } clone swap [ 42 over push ] times ] call ] unit-test
{ vector } [ [ V{ } clone swap [ 42 over push ] times ] final-classes first ] unit-test
{ f } [ [ V{ } clone swap [ 42 over push ] times length ] final-literals first ] unit-test
{ f } [ [ [ V{ } clone swap [ 42 over push ] times length ] final-literals ] with-rw first ] unit-test
{ f } [ [ [ { vector } declare swap [ 42 over push ] times length ] final-literals ] with-rw first ] unit-test

! Counter variable in rw-tuple
: test-loop ( limit num counter-box -- limit num counter-box )
    [ [ 1 + ] dip [ 1 + ] change-a dup a>> reach < ] loop ; inline
{ 5 42 T{ box f 5 } } [ 5 37 0 <box> [ test-loop ] call ] unit-test
{ V{ real number object } } [ [ test-loop ] final-classes ] unit-test
{ V{ real number object } } [ [ [ test-loop ] final-classes ] with-rw ] unit-test

! using locals
:: test-loop-locals ( limit num counter-box -- limit num counter-box )
    limit num [ 1 + counter-box [ 1 + ] change-a drop counter-box a>> pick < ] loop
    counter-box ; inline
{ 5 42 T{ box f 5 } } [ 5 37 0 <box> [ test-loop-locals ] call ] unit-test
{ V{ real number object } } [ [ test-loop-locals ] final-classes ] unit-test
{ V{ real number object } } [ [ [ test-loop-locals ] final-classes ] with-rw ] unit-test

! Comparison version without box
: test-append-normal ( limit -- vector )
    V{ } clone swap
    0
    [ dup pick < ] [ 42 reach push 1 + ] while
    2drop ; inline

{ V{ 42 42 42 } } [ 3 [ test-append-normal ] call ] unit-test
{ vector } [ [ test-append-normal ] final-classes first ] unit-test
! FIXME
{ vector } [ [ [ test-append-normal ] final-info first ] with-rw ] unit-test

! Not using locals, appending
: test-append ( limit -- vector )
    V{ } clone swap
    0 <box>
    [ dup a>> pick < ] [ 42 reach push [ 1 + ] change-a ] while
    2drop ; inline

{ V{ 42 42 42 } } [ 3 [ test-append ] call ] unit-test
{ vector } [ [ test-append ] final-classes first ] unit-test
! FIXME
{ vector } [ [ [ test-append ] final-classes first ] with-rw ] unit-test

! Using locals, appending
:: test-fun ( limit -- vector )
    V{ } clone :> acc
    0 <box> :> counter-box
    [ counter-box a>> limit < ] [ 42 acc push counter-box [ 1 + ] change-a drop ] while
    acc ; inline

{ V{ 42 42 42 } } [ 3 [ test-fun ] call ] unit-test
{ vector } [ [ test-fun ] final-classes first ] unit-test
{ vector } [ [ [ test-fun ] final-classes first ] with-rw ] unit-test

! Letting the box escape in the loop
:: test-fun-frob ( limit -- vector )
    V{ } clone :> acc
    0 <box> :> counter-box
    [ counter-box a>> limit < ] [ 42 acc push counter-box [ 1 + ] change-a frob ] while
    acc ; inline

{ V{ 42 42 42 } } [ 3 [ test-fun-frob ] call ] unit-test
{ vector } [ [ test-fun-frob ] final-classes first ] unit-test
{ vector } [ [ [ test-fun-frob ] final-classes first ] with-rw ] unit-test

! Counter variable in rw-tuple, limit in tuple
:: test-fun-2 ( limit-box -- vector )
    V{ } clone :> acc
    0 <box> :> counter-box
    [ counter-box limit-box [ a>> ] bi@ < ] [ 42 acc push counter-box [ 1 + ] change-a drop ] while
    acc ; inline

{ V{ 42 42 42 } } [ 3 <box> [ test-fun-2 ] call ] unit-test
{ vector } [ [ test-fun-2 ] final-classes first ] unit-test
{ vector } [ [ [ test-fun-2 ] final-classes first ] with-rw ] unit-test


! ONLY works when loaded twice
! TUPLE: circle { me circle } ;

! Infinite runtime loops
{ null } [ [ [ 1 + dup ] loop ] final-classes first ] unit-test
{ null } [ [ [ [ 1 + dup ] loop ] final-classes first ] with-rw ] unit-test
! Recursive access
{ array } [ [ [ box new [ a>> ] follow ] final-classes first ] with-rw ] unit-test
{ array } [ [ [ box new [ { box } declare a>> ] follow ] final-classes first ] with-rw ] unit-test
! Recursive access with slot-declaration
! { } [ [ [ circle new [ me>> ] follow ] final-info ] with-rw ] unit-test


! Test for the #1370 bug
STRUCT: sbar { s sbar* } ;

{ t } [
    [ [ sbar <struct> [ s>> ] follow ] final-info ]  with-rw
    ! [ #recursive? ] find nip
    ! child>> [ { [ #call? ] [ word>> \ alien-cell = ] } 1&& ] find nip
    ! >boolean
] unit-test
