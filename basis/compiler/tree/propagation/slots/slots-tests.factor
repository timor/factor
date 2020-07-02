USING: accessors arrays assocs compiler.tree compiler.tree.propagation.copy
compiler.tree.propagation.info compiler.tree.propagation.slots hashtables kernel
math math.intervals namespaces sequences slots.private tools.test ;
IN: compiler.tree.propagation.slots.tests

: indexize ( seq -- assoc )
    [ swap 2array ] map-index ;

: setup-value-infos ( value-infos -- )
    indexize >hashtable 1array value-infos set
    H{ { 0 0 } { 1 1 } { 2 2 } } copies set ;

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

TUPLE: dummy a ;
CONSTANT: test-slot 5
CONSTANT: test-val 42

: setup-test-values ( -- )
    dummy <class-info> 1array ${ ! 0
        test-slot                ! 1
        test-val                 ! 2
        test-val 1 +             ! 3
        5                        ! 4
    }
    [ <literal-info> ] map append
    [ length <iota> introduce-values ]
    [ <enumerated> >hashtable 1array value-infos set ] bi
    V{  } clone slot-states set
    ;

! Testing update-slot-state
{ 1 } [
    setup-test-values
    2 0 1 update-slot-state
    slot-states get length
] unit-test

! Test effect of update-slot-state in propagate-after
{ 1 } [
    setup-test-values
    { 2 0 1 } {  } \ set-slot <#call>
    set-slot-call-propagate-after
    slot-states get length
] unit-test

{ +same-slot+ } [
    setup-test-values
    { 2 0 1 } {  } \ set-slot <#call>
    set-slot-call-propagate-after
    slot-states get first
    2 0 1 <slot-state> compare-slot-states
] unit-test

! Test overwrite of slot
{ 2 } [
    setup-test-values
    { 2 0 1 } {  } \ set-slot <#call>
    set-slot-call-propagate-after
    { 3 0 1 } {  } \ set-slot <#call>
    set-slot-call-propagate-after
    slot-states get length
] unit-test

! Test non-override of slot
{ 3 } [
    setup-test-values
    { 2 0 1 } {  } \ set-slot <#call>
    set-slot-call-propagate-after
    { 2 0 3 } {  } \ set-slot <#call>
    set-slot-call-propagate-after
    { 2 1 3 } {  } \ set-slot <#call>
    set-slot-call-propagate-after
    slot-states get length
] unit-test

: propagated-tree ( quot -- nodes )
    build-tree analyze-recursive normalize propagate
    cleanup-tree ;

: extract-slots ( quot -- nodes slot-states query-states )
    propagated-tree dup
    slot-states get swap [ dup slot-call? [ drop f ] unless ] map-nodes flatten
    [ f swap in-d>> resolve-copies first2 <slot-state> ] map
    ;

{ +same-slot+ } [
    [| a! | 13 a! 14 a! ] extract-slots
    drop first2 compare-slot-states nip
] unit-test

{ +same-slot+ } [
    [| a! | 13 a! a ] extract-slots
    [ first ] bi@ compare-slot-states nip
] unit-test

{ { +same-slot+ +unrelated+ +may-alias+ } } [
    [| a b c | 42 a 3 set-slot a 3 slot b 4 slot c 3 slot ] extract-slots
    [ first ] dip [ compare-slot-states ] with map nip
] unit-test

{ V{ +may-alias+ +may-alias+ +may-alias+ } } [
    [| a b c s1 s2 s3 |
     42 a s1 set-slot
     69 b s2 set-slot
     99 c s3 set-slot
     c 5 slot
    ] extract-slots
    first swap [ compare-slot-states ] with map nip
] unit-test
