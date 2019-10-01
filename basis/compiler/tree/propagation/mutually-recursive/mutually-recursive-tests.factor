USING: accessors arrays combinators compiler compiler.tree compiler.tree.builder
compiler.tree.normalization compiler.tree.propagation
compiler.tree.propagation.info compiler.tree.propagation.inlining
compiler.tree.propagation.mutually-recursive
compiler.tree.propagation.mutually-recursive.interface
compiler.tree.propagation.mutually-recursive.pruning compiler.tree.recursive
kernel kernel.private locals math math.intervals math.private namespaces
sequences tools.annotations tools.test typed words ;
IN: compiler.tree.propagation.mutually-recursive.tests

: normalized-tree ( quot/word -- nodes )
    build-tree analyze-recursive normalize ;

: tword ( word -- word )
    "typed-word" word-prop ;

: with-vars ( quot -- )
    V{ } clone check-call-sites rot with-variable ; inline

:: rec-test ( word -- nodes )
    H{ { propagate-recursive? t }
       { check-call-sites V{ } } } [ word start-compilation word normalized-tree
                           ! \ is-copy-of watch
                           \ inline-recursive-call reset
                           \ inline-recursive-call watch
                           propagate
                           ! \ is-copy-of reset
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

{ 42 } [ \ bar2 rec-test last node-input-infos first literal>> ] unit-test

{ f } [ foo-call dup clone = ] unit-test
{ t } [ foo-call dup clone call= ] unit-test

{ f } [ [ foo-call foo-tree [ reject-call ] keep = ] with-vars ] unit-test
{ f } [ [ foo-call foo-tree reject-call foo-tree = ] with-vars ] unit-test


! Associating call sites
{ t } [
    test-if { t f } <inlined-call-site>
    test-tree swap complete-call-site phi>> test-phi = ] unit-test

{ t } [ [ test-call test-if reject-call* drop
                      check-call-sites get pop
                      inlined-call-site? ]
        with-vars ] unit-test

{ t { f t } } [ [
            test-call test-if reject-call* drop
            test-tree complete-last-call-site
            check-call-sites get pop
            [ phi>> test-phi = ]
            [ remaining-branches>> ] bi
          ] with-vars ] unit-test

! Diverging call site info
CONSTANT: info1
T{ value-info-state
   { class fixnum }
   { interval T{ interval { from { 34 t } } { to { 50 t } } } }
 }

CONSTANT: info2
T{ value-info-state
   { class fixnum }
   { interval T{ interval { from { 34 t } } { to { 60 t } } } }
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

{ f f } [ info2 info1 [ lower-bound-diverges? ] [ upper-bound-diverges? ] 2bi ] unit-test
{ f t } [ info1 info2 [ lower-bound-diverges? ] [ upper-bound-diverges? ] 2bi ] unit-test
{ t t } [ info1 info4 [ lower-bound-diverges? ] [ upper-bound-diverges? ] 2bi ] unit-test
{ t f } [ info1 info3 [ lower-bound-diverges? ] [ upper-bound-diverges? ] 2bi ] unit-test

! Making distinction between inputs from base-case branches and recursive call site branches

{
    V{ T{ value-info-state
          { class fixnum }
          { interval
            T{ interval { from { 20 t } } { to { 45 t } } } } } }
    T{ value-info-state
       { class fixnum }
       { interval T{ interval { from { 34 t } } { to { 60 t } } } } }
} [ info1 info2 info3 3array { t t f } merge-base-case-infos ] unit-test


! Handle divergence detection
{ -1/0. 50 } [ info1 clone info3 diverge-info interval>> interval>points [ first ] bi@ ] unit-test
{ 20 1/0. } [ info3 clone info2 diverge-info interval>> interval>points [ first ] bi@ ] unit-test
{ t } [ info3 clone info4 diverge-info interval>> full-interval? ] unit-test

{ t } [ info1 clone info3 info2 2array swap [ diverge-info ] reduce interval>> full-interval? ] unit-test

CONSTANT: rec-phi T{ #phi
   { phi-in-d { { 26307994 } { 26307995 } } }
   { phi-info-d
     {
         {
             T{ value-info-state
                { class fixnum }
                { interval T{ interval { from { 20 t } } { to { 45 t } } } }
              }
         }
         {
             T{ value-info-state
                { class fixnum }
                { interval
                  T{ interval
                     { from { 42 t } }
                     { to { 42 t } }
                   }
                }
                { literal 42 }
                { literal? t }
              }
         }
     }
   }
   { out-d V{ 26307479 } }
   { terminated { f f } }
 }

{ -1/0. 1/0. } [ rec-phi phi-info-d>> { f t } diverge-phi-infos first interval>> interval>points [ first ] bi@ ] unit-test
{ 20 45 } [ rec-phi phi-info-d>> { t f } diverge-phi-infos first interval>> interval>points [ first ] bi@ ] unit-test
