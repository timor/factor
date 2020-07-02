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
    dummy <class-info> 1array ${ test-slot test-val test-val 1 + }
    [ <literal-info> ] map append
    [ length <iota> introduce-values ]
    [ <enumerated> >hashtable 1array value-infos set ] bi
    H{  } clone slot-states set
    ;

! Testing update-slot-state
{ 0 1 2 } [
    setup-test-values
    2 0 1 update-slot-state
    slot-states get >alist first first2 >alist first first2
    copy-of>>
] unit-test

! Test effect of update-slot-state in propagate-after
{ 0 1 2 } [
    setup-test-values
    { 2 0 1 } {  } \ set-slot <#call>
    set-slot-call-propagate-after
    slot-states get >alist first first2 >alist first first2
    copy-of>>
] unit-test

! Test overwrite of slot
{ 1 0 1 3 } [
    setup-test-values
    { 2 0 1 } {  } \ set-slot <#call>
    set-slot-call-propagate-after
    { 3 0 1 } {  } \ set-slot <#call>
    set-slot-call-propagate-after
    slot-states get >alist [ length ] keep
    first first2 >alist first first2
    copy-of>>
] unit-test
