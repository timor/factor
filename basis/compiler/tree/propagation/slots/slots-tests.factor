USING: accessors arrays assocs compiler.tree compiler.tree.builder
compiler.tree.cleanup compiler.tree.combinators compiler.tree.normalization
compiler.tree.propagation compiler.tree.propagation.branches
compiler.tree.propagation.copy compiler.tree.propagation.info
compiler.tree.propagation.nodes compiler.tree.propagation.slots
compiler.tree.recursive grouping.extras hashtables kernel kernel.private literals locals math
math.intervals namespaces sequences sequences.deep sets slots.private tools.test
;
IN: compiler.tree.propagation.slots.tests

FROM: namespaces => set ;

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

: alias-relations ( slot-states -- assoc )
    dup dup [ [ compare-slot-states ] keep 2array ] cartesian-map zip
    [ [ first ] group-by [ [ second ] map ] assoc-map >hashtable ] assoc-map >hashtable ;

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

! Testing slot-call-update-slot-state
{ 1 } [
    setup-test-values
    2 0 1 slot-call-update-slot-state
    slot-states get length
] unit-test

! Test effect of slot-call-update-slot-state in propagate-after
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

! * Test removing assumptions when tuple escapes

: dummy-user ( obj -- ) { dummy } declare [ 1 + ] change-a drop ;

! Feeding copy of tuple to call, can be anything afterwards
${ 1 0 } [
    setup-test-values
    { 2 0 1 } {  } \ set-slot <#call>
    set-slot-call-propagate-after
    slot-states get length
    { 0 } { } \ dummy-user <#call>
    [ [ compute-copy-equiv ] [ propagate-around ] bi ] keep
    invalidate-slot-states
    slot-states get length
] unit-test

! * Test overwrite of slot
{ 1 } [
    setup-test-values
    { 2 0 1 } {  } \ set-slot <#call>
    set-slot-call-propagate-after
    { 3 0 1 } {  } \ set-slot <#call>
    set-slot-call-propagate-after
    slot-states get length
] unit-test

! * Test non-override of slot
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
    ! cleanup-tree
    ;

: extract-slot-calls ( nodes -- seq )
    [ dup slot-call? [ drop f ] unless ] map-nodes flatten ;

: extract-tuple-boa-calls ( nodes -- seq )
    [ dup tuple-boa-call? [ drop f ] unless ] map-nodes flatten ;

: extract-slots ( quot -- nodes slot-states query-states )
    propagated-tree dup
    slot-states get swap extract-slot-calls
    [ in-d>> resolve-copies first2 <unknown-slot-state> ] map
    ;

! * Testing determining aliasing slot calls
! Testing whether we broke compilation of `extract-slots` and `extract-slot-calls`
{ +same-slot+ } [
    [| a! | 13 a! a ]
    propagated-tree dup
    slot-states get swap [ dup slot-call? [ drop f ] unless ] map-nodes flatten
    [ in-d>> resolve-copies first2 <unknown-slot-state> ] map
    [ first ] bi@ compare-slot-states nip
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

{ V{ +same-slot+ +unrelated+ +unrelated+ +unrelated+ +unrelated+ } } [
    [| a b s1 s2 |
     a { tuple } declare
     b { array } declare
     10 a s1 set-slot
     11 b s1 set-slot
     12 b s2 set-slot
     20 { 1 2 3 } s1 set-slot
     30 { 1 2 3 } s2 set-slot
     a s1 slot
    ] extract-slots
    first swap [ compare-slot-states ] with map nip
] unit-test

{ V{ 43 69 70 77 80 81 } } [| |
    [| a b c s1 s2 s3 |
     42 a s1 set-slot
     43 a s1 set-slot
     69 b s1 set-slot
     70 b s2 set-slot
     77 c s3 set-slot
     80 c s1 set-slot
     81 c 3 set-slot
     a { tuple } declare
     82 { 1 2 3 } 3 set-slot
     a s1 slot
    ] extract-slots :> ( nodes states queries )
    states queries first select-aliasing-read
    <reversed> [ value-info>> literal>> ] map
] unit-test

! Querying simple slots should work
{ 12 13 } [
    [| a |
     12 a 3 set-slot
     13 a 4 set-slot
     a 3 slot
     a 4 slot
    ] extract-slots 2nip
    [ [ obj-value>> ] [ slot-value>> ] bi slot-query-state value-info>> literal>> ] map
    first2
] unit-test

${ 5 42 [a,b] } [
    [| a b c s1 s2 s3 |
     a { tuple } declare
     5 a s1 set-slot
     13 b s2 set-slot
     99 { 1 2 3 4 } s3 set-slot
     42 c s3 set-slot
     a s1 slot
    ] extract-slots 2nip
    first [ obj-value>> ] [ slot-value>> ] bi
    slot-query-state value-info>> interval>>
] unit-test

{ 1 t } [
    [| a b s1 s2 |
     a { tuple } declare
     b { array } declare
     5 a s1 set-slot
     6 b s2 set-slot
     a s1 slot
    ] extract-slots 2nip
    first [ obj-value>> ] [ slot-value>> ] bi
    slot-query-state copy-of>> [ length ] [ first fixnum? ] bi
] unit-test

{ 1 t } [
    [| a b s1 s2 |
     a { tuple } declare
     10 a s1 set-slot
     a b s2 set-slot
     b s2 slot
    ] extract-slots 2nip
    first [ obj-value>> ] [ slot-value>> ] bi
    slot-query-state copy-of>> [ length ] [ first fixnum? ] bi
] unit-test

! different objects, different slot literals with equal value, same value
! slot accesses to any other must be unknown
${ t f object-info } [
    [| a b x |
     x a 11 set-slot
     x b 11 set-slot
     a 11 slot
     a 10 slot
    ] extract-slots 2nip
    [ [ obj-value>> ] [ slot-value>> ] bi slot-query-state ] map
    first2
    [ slot-copy fixnum? ]
    [ [ slot-copy ] [ value-info>> ] bi ] bi*
] unit-test

! * Nested tuples
TUPLE: dummy2 b ;

: nested-slot-states-quot ( -- quot )
    [ { dummy dummy2 } declare 42 >>b >>a a>> b>> ] ;

{ V{ 1 2 } } [
    nested-slot-states-quot propagated-tree drop
    slot-states get
    [ all-dependent-slot-states length ] map
] unit-test

{ V{ 2 2 } } [
    [ { dummy dummy } declare [ >>a ] [ swap >>a ] 2bi [ a>> ] bi@ ]
    propagated-tree drop
    slot-states get
    [ all-dependent-slot-states length ] map
] unit-test

{ V{ 1 } } [
    [ { dummy } declare dup >>a a>> ] propagated-tree drop
    slot-states get
    [ all-dependent-slot-states length ] map
] unit-test

: flushable-dummy-user ( obj -- ) { dummy } declare [ 1 + ] change-a drop ; flushable

{ V{ 2 } } [
    [ { dummy dummy } declare 69 >>a >>a flushable-dummy-user ] propagated-tree
    flatten [ dup #call? [ word>> \ flushable-dummy-user eq? ] [ drop f ] if ] filter first
    in-d>> [ obj-value-slot-states [ all-dependent-slot-states ] map concat length ] map
] unit-test

! * Annotating nodes

! Output info is set via copying info
{ t 42 42 } [
    [| a s1 |
     42 a s1 set-slot
     a s1 slot
    ] extract-slots nip
    first [ obj-value>> ] [ slot-value>> ] bi slot-query-state
    [ slot-copy fixnum? ] [ value-info>> literal>> ] bi
    rot
    extract-slot-calls first
    [ refine-slot-call-outputs ]
    [ annotate-node ]
    [ node-output-infos first literal>> ] tri
] unit-test

! If we don't create a copy, we modify the value-info states.  This happens if
! we alias, but infer the same value info.
{ 42 } [
    [| a b s1 s2 |
     42 a s1 set-slot
     42 b s1 set-slot
     42 a s2 set-slot
     42 b s2 set-slot
     a s1 slot
    ] extract-slots 2drop
    extract-slot-calls first
    [ refine-slot-call-outputs ]
    [ annotate-node ]
    [ node-output-infos first literal>> ] tri
] unit-test

! Merging sets of states

! 3 identical sets of unrelated accesses merged should be equal to the original
{ t } [
    [| a b c |
     10 a 1 set-slot
     20 b 2 set-slot
     30 { 1 2 3 } 3 set-slot
    ] extract-slots drop nip
    dup dup 3array merge-slot-states
    slot-states get set=
] unit-test

{ 4 t } [
    [| a b s1 s2 |
     10 a s1 set-slot
     20 b s2 set-slot
    ] extract-slots drop nip
    [| a b s1 s2 |
     5 a s1 set-slot
     40 b s2 set-slot
    ] extract-slots drop nip
    2array merge-slot-states
    [ length ]
    [ [ value-info>> interval>> 5 40 [a,b] = ] all? ] bi
] unit-test

! * More testing of removing assumptions on escape

! Everything aliases, nothing can be assumed
${ 0 object-info dup dup dup  } [
    [| a b s1 s2 |
    10 a s1 set-slot
    11 a s2 set-slot
    20 b s1 set-slot
    21 b s2 set-slot
    a dummy-user
    a s1 slot
    a s2 slot
    b s1 slot
    b s2 slot ] propagated-tree
    extract-slot-calls slot-states get swap
    [ length ] [ [ out-d>> first value-info ] map first4 ] bi*
] unit-test

! test that unrelated info is unrelated
{ { 0 0 2 2  } } [
    [| a b s1 s2 |
     10 a { dummy } declare s1 set-slot
     11 a { dummy } declare s2 set-slot
     20 b { array } declare s1 set-slot
     21 b { array } declare s2 set-slot
     a { dummy } declare dummy-user
     a s1 slot
     a s2 slot
     b s1 slot
     b s2 slot ] propagated-tree
    extract-slot-calls
    [ in-d>> resolve-copies first ] map
    [ obj-value-slot-states [ aliasing-slot-states ] map concat members ] map
    [ length ] map
] unit-test

{ 2 } [
    [| a b s1 s2 |
     10 a { dummy } declare s1 set-slot
     11 a { dummy } declare s2 set-slot
     20 b { array } declare s1 set-slot
     21 b { array } declare s2 set-slot
     a dummy-user
     a s1 slot
     a s2 slot
     b s1 slot
     b s2 slot ] propagated-tree drop
    slot-states get length
] unit-test

! * Test branch information

! same object, same slot, different value but with same value-info
{ 1 5 } [
    [ [ 5 -rot set-slot ] [ 5 -rot set-slot ] if ] extract-slots 3drop
    infer-children-data get [ slot-states of ] map
    merge-slot-states
    [ length ]
    [ first value-info>> literal>> ] bi
] unit-test

! same object, same slot, different value-info
${ 1 4 8 [a,b] } [
    [ [ 4 -rot set-slot ] [ 8 -rot set-slot ] if ] extract-slots 3drop
    infer-children-data get [ slot-states of ] map
    merge-slot-states
    [ length ]
    [ first value-info>> interval>> ] bi
] unit-test

! same thing, but with locals.
${ 2 4 8 [a,b] dup } [
    [| a! | [ 4 a! ] [ 8 a! ] if a ] extract-slots 3drop
    infer-children-data get [ slot-states of ] map
    merge-slot-states
    [ length ]
    [ [ value-info>> interval>> ] map first2 ] bi
] unit-test

! same thing, using the interface function from branches
${ 2 4 8 [a,b] dup } [
    [| a! | [ 4 a! ] [ 8 a! ] if a ] extract-slots 3drop
    branch-slot-states
    slot-states get
    [ length ]
    [ [ value-info>> interval>> ] map first2 ] bi
] unit-test

${ 2 4 8 [a,b] dup } [
    [| a! | [ 4 a! ] [ 8 a! ] if a ] extract-slots 3drop
    slot-states get dup .
    [ length ]
    [ [ value-info>> interval>> ] map first2 ] bi
] unit-test

! Setting value before the branch, overriding in one
! NOTE: after tracking through currieds work, this should only contain 1 slot
! state
${ 2 4 5 [a,b] } [
    [| a! | 4 a! [ 5 a! ] [  ] if a ] extract-slots 3drop
    infer-children-data get [ slot-states of ] map
    slot-states get suffix
    merge-slot-states
    [ length ]
    [ first value-info>> interval>> ] bi
] unit-test

! * SSA value copy computation

! For copy slot, check that the SSA values of the set-slot call match with the
! resolved output value after updating copy information
{ t t } [
    [| a s1 |
     42 a s1 set-slot
     a s1 slot ] extract-slots drop swap
    extract-slot-calls first
    [ slot-call-compute-copy-equiv* ]
    [ out-d>> first resolve-copy ] bi
    swap first slot-copy
    [ [ fixnum? ] both? ]
    [ = ] 2bi
] unit-test

! * Tuple-boa and tuple literal slot info

TUPLE: mixed { ro read-only } rw ;

! Propagating SSA value copy information on literal tuples
{ V{ t t } 2 } [
    [| x | x dup dup mixed boa ] propagated-tree
    [ last in-d>> first resolve-copy ] keep
    extract-tuple-boa-calls first
    tuple-boa-call-propagate-after
    slot-states get
    [ [ slot-copy = ] with map ]
    [ length ] bi
] unit-test

! Same with method call
{ V{ t t } 2 } [
    [| x | x dup dup mixed boa ] propagated-tree
    last in-d>> first resolve-copy
    slot-states get
    [ [ slot-copy = ] with map ]
    [ length ] bi
] unit-test
