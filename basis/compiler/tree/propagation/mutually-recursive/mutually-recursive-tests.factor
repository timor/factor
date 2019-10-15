USING: accessors arrays compiler compiler.tree.propagation
compiler.tree.propagation.info compiler.tree.propagation.inlining
compiler.tree.propagation.mutually-recursive
compiler.tree.propagation.mutually-recursive.interface
compiler.tree.propagation.mutually-recursive.pruning kernel kernel.private
locals math math.intervals namespaces sequences tools.annotations tools.test
words ;
IN: compiler.tree.propagation.mutually-recursive.tests

: tword ( word -- word )
    "typed-word" word-prop ;

:: rec-test ( word -- nodes )
    H{ { propagate-recursive? t }
    } [ word start-compilation word normalized-tree
        \ inline-recursive-call reset
        \ inline-recursive-call watch
        propagate
        \ inline-recursive-call reset
    ] with-variables ;

! * Single call site
{ t } [ test-call test-if children>> first child-contains-node? ] unit-test
{ f } [ test-call test-if children>> second child-contains-node? ] unit-test


: baz-test ( -- x )
    propagate-recursive? [ \ baz tword dup start-compilation normalized-tree propagate ] with-variable-on ;

: bar ( x -- y )
    { fixnum } declare dup 9 > [ drop 42 ] [ 4 + bar ] if ;

{ 42 } [ \ bar rec-test last node-input-infos first literal>> ] unit-test

! * Multiple Call Sites

: bar2 ( x -- y )
    { fixnum } declare
    dup odd? [ 3 + bar2 ] [
        dup 5 > [ drop 42 ] [ 5 + bar2 ] if
    ] if ;

! FIXME: infers union type { fixnum, f }
{ 42 42 } [ \ bar2 rec-test last node-input-infos first interval>> interval>points [ first ] bi@ ] unit-test

{ f } [ foo-call dup clone = ] unit-test
{ t } [ foo-call dup clone call= ] unit-test

! Diverging call site info
CONSTANT: info1
T{ value-info-state
   { class fixnum }
   { interval T{ interval { from { 34 t } } { to { 50 t } } } }
 }

CONSTANT: info2
T{ value-info-state
   { class fixnum }
   { interval T{ interval { from { 35 t } } { to { 60 t } } } }
 }

CONSTANT: info3
T{ value-info-state
   { class fixnum }
   { interval T{ interval { from { 20 t } } { to { 45 t } } } }
 }

CONSTANT: info4
T{ value-info-state
   { class fixnum }
   { interval T{ interval { from { 10 t } } { to { 60 t } } } }
 }

{ t f } [ info2 info1 [ interval>> ] bi@ [ lower-bound-diverges? ] [ upper-bound-diverges? ] 2bi ] unit-test
{ f t } [ info1 info2 [ interval>> ] bi@ [ lower-bound-diverges? ] [ upper-bound-diverges? ] 2bi ] unit-test
{ t t } [ info1 info4 [ interval>> ] bi@ [ lower-bound-diverges? ] [ upper-bound-diverges? ] 2bi ] unit-test
{ t f } [ info1 info3 [ interval>> ] bi@ [ lower-bound-diverges? ] [ upper-bound-diverges? ] 2bi ] unit-test


! Handle divergence detection
! On intervals
CONSTANT: i1 T{ interval { from { -20 t } } { to { 40 t } } }
CONSTANT: i2 T{ interval { from { -20 t } } { to { 30 t } } }

{ -20 30 } [ i1 1array i2 diverge-info-intervals interval>points [ first ] bi@ ] unit-test
{ -20 1/0. } [ i2 1array i1 diverge-info-intervals interval>points [ first ] bi@ ] unit-test

CONSTANT: i3 T{ interval { from { -25 t } } { to { 30 t } } }

{ -20 30 } [ i3 1array i2 diverge-info-intervals interval>points [ first ] bi@ ] unit-test
{ -1/0. 30 } [ i2 1array i3 diverge-info-intervals interval>points [ first ] bi@ ] unit-test

{ -20 30 } [ i3 i1 2array i2 diverge-info-intervals interval>points [ first ] bi@ ] unit-test
{ -20 1/0. } [ i2 i3 2array i1 diverge-info-intervals interval>points [ first ] bi@ ] unit-test

! On infos
{ 34 50 } [ info3 1array info1 diverge-info interval>> interval>points [ first ] bi@ ] unit-test
{ 35 1/0. } [ info1 1array info2 diverge-info interval>> interval>points [ first ] bi@ ] unit-test
{ t } [ info3 1array info4 diverge-info interval>> full-interval? ] unit-test
{ 34 50 } [ info4 info3 2array info1 diverge-info interval>> interval>points [ first ] bi@ ] unit-test
