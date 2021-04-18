USING: accessors arrays classes.tuple.private compiler.test compiler.tree
compiler.tree.propagation.copy compiler.tree.propagation.info
compiler.tree.propagation.slots hashtables kernel math math.intervals namespaces
sequences stack-checker.values tools.test vectors words ;
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
