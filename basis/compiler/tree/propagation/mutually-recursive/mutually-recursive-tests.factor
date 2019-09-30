USING: accessors arrays combinators compiler compiler.tree compiler.tree.builder
compiler.tree.normalization compiler.tree.propagation
compiler.tree.propagation.copy compiler.tree.propagation.info
compiler.tree.propagation.inlining compiler.tree.propagation.mutually-recursive
compiler.tree.recursive kernel kernel.private locals math math.intervals
math.private namespaces sequences tools.annotations tools.test typed words ;
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
TYPED: baz ( x: fixnum -- y )
         dup 5 > [ 1 - baz ] [ drop 42 ] if ;

CONSTANT: test-tree
{
    T{ #introduce { out-d { 26307480 } } }
    T{ #shuffle
        { mapping
            { { 26307456 26307480 } { 26307457 26307480 } }
        }
        { in-d V{ 26307480 } }
        { out-d V{ 26307456 26307457 } }
    }
    T{ #push { literal 5 } { out-d { 26307458 } } }
    T{ #call
        { word fixnum> }
        { in-d V{ 26307457 26307458 } }
        { out-d { 26307481 } }
        { info
            H{
                {
                    26307457
                    T{ value-info-state
                        { class fixnum }
                        { interval
                            T{ interval
                                { from
                                    { -576460752303423488 t }
                                }
                                { to { 576460752303423487 t } }
                            }
                        }
                    }
                }
                {
                    26307458
                    T{ value-info-state
                        { class fixnum }
                        { interval
                            T{ interval
                                { from { 5 t } }
                                { to { 5 t } }
                            }
                        }
                        { literal 5 }
                        { literal? t }
                    }
                }
                {
                    26307481
                    T{ value-info-state
                        { class object }
                        { interval full-interval }
                    }
                }
            }
        }
    }
    T{ #if
        { in-d { 26307459 } }
        { children
            {
                {
                    T{ #push
                        { literal 1 }
                        { out-d { 26307460 } }
                    }
                    T{ #call
                        { word fixnum-fast }
                        { in-d V{ 26307456 26307460 } }
                        { out-d { 26307482 } }
                        { info
                            H{
                                {
                                    26307456
                                    T{ value-info-state
                                        { class fixnum }
                                        { interval
                                            T{ interval
                                                { from { 6 t } }
                                                { to
                                                    {
                                                        576460752303423487
                                                        t
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                                {
                                    26307482
                                    T{ value-info-state
                                        { class fixnum }
                                        { interval
                                            T{ interval
                                                { from { 5 t } }
                                                { to
                                                    {
                                                        576460752303423486
                                                        t
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                                {
                                    26307460
                                    T{ value-info-state
                                        { class fixnum }
                                        { interval
                                            T{ interval
                                                { from { 1 t } }
                                                { to { 1 t } }
                                            }
                                        }
                                        { literal 1 }
                                        { literal? t }
                                    }
                                }
                            }
                        }
                    }
                    T{ #call
                        { word baz }
                        { in-d V{ 26307476 } }
                        { out-d { 26307477 } }
                        { info
                            H{
                                {
                                    26307476
                                    T{ value-info-state
                                        { class fixnum }
                                        { interval
                                            T{ interval
                                                { from { 5 t } }
                                                { to
                                                    {
                                                        576460752303423486
                                                        t
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                                {
                                    26307477
                                    T{ value-info-state
                                        { class object }
                                        { interval
                                            full-interval
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                {
                    T{ #shuffle
                        { mapping { } }
                        { in-d V{ 26307456 } }
                        { out-d V{ } }
                    }
                    T{ #push
                        { literal 42 }
                        { out-d { 26307478 } }
                    }
                }
            }
        }
        { live-branches { t t } }
    }
    T{ #phi
        { phi-in-d { { 26307994 } { 26307995 } } }
        { phi-info-d
            {
                {
                    T{ value-info-state
                        { class object }
                        { interval full-interval }
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
    T{ #return
        { in-d V{ 26307479 } }
        { info
            H{
                {
                    26307479
                    T{ value-info-state
                        { class object }
                        { interval full-interval }
                    }
                }
            }
        }
    }
}

: test-if ( -- if )
    4 test-tree nth ;

: test-phi ( -- phi )
    5 test-tree nth ;

: test-call ( -- call )
    test-if children>> first third ;

: test-base-case-branch ( -- nodes )
    test-if children>> second ;

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

: foo ( x -- x )
    { { [ dup 0 > ] [ dup 1 - foo - ] }
      { [ dup abs 100 > ] [ dup 2 /i foo - ] }
      [ drop 42 ]
    } cond ;

CONSTANT: foo-tree
{
    T{ #introduce { out-d { 27086769 } } }
    T{ #shuffle
        { mapping
            { { 27086743 27086769 } { 27086744 27086769 } }
        }
        { in-d V{ 27086769 } }
        { out-d V{ 27086743 27086744 } }
    }
    T{ #push { literal 0 } { out-d { 27086745 } } }
    T{ #call
        { word > }
        { in-d V{ 27086744 27086745 } }
        { out-d { 27086746 } }
        { info
            H{
                {
                    27086744
                    T{ value-info-state
                        { class object }
                        { interval full-interval }
                    }
                }
                {
                    27086745
                    T{ value-info-state
                        { class fixnum }
                        { interval
                            T{ interval
                                { from { 0 t } }
                                { to { 0 t } }
                            }
                        }
                        { literal 0 }
                        { literal? t }
                    }
                }
                {
                    27086746
                    T{ value-info-state
                        { class object }
                        { interval full-interval }
                    }
                }
            }
        }
    }
    T{ #if
        { in-d { 27086746 } }
        { children
            {
                {
                    T{ #shuffle
                        { mapping
                            {
                                { 27086747 27086743 }
                                { 27086748 27086743 }
                            }
                        }
                        { in-d V{ 27086743 } }
                        { out-d V{ 27086747 27086748 } }
                    }
                    T{ #push
                        { literal 1 }
                        { out-d { 27086749 } }
                    }
                    T{ #call
                        { word - }
                        { in-d V{ 27086748 27086749 } }
                        { out-d { 27086750 } }
                        { info
                            H{
                                {
                                    27086748
                                    T{ value-info-state
                                        { class real }
                                        { interval
                                            T{ interval
                                                { from { 0 f } }
                                                { to
                                                    { 1/0. t }
                                                }
                                            }
                                        }
                                    }
                                }
                                {
                                    27086749
                                    T{ value-info-state
                                        { class fixnum }
                                        { interval
                                            T{ interval
                                                { from { 1 t } }
                                                { to { 1 t } }
                                            }
                                        }
                                        { literal 1 }
                                        { literal? t }
                                    }
                                }
                                {
                                    27086750
                                    T{ value-info-state
                                        { class real }
                                        { interval
                                            T{ interval
                                                { from
                                                    { -1 f }
                                                }
                                                { to
                                                    { 1/0. t }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                    T{ #call
                        { word foo }
                        { in-d V{ 27086750 } }
                        { out-d { 27086751 } }
                        { info
                            H{
                                {
                                    27086750
                                    T{ value-info-state
                                        { class real }
                                        { interval
                                            T{ interval
                                                { from
                                                    { -1 f }
                                                }
                                                { to
                                                    { 1/0. t }
                                                }
                                            }
                                        }
                                    }
                                }
                                {
                                    27086751
                                    T{ value-info-state
                                        { class number }
                                        { interval
                                            full-interval
                                        }
                                    }
                                }
                            }
                        }
                    }
                    T{ #call
                        { word - }
                        { in-d V{ 27086747 27086751 } }
                        { out-d { 27086752 } }
                        { info
                            H{
                                {
                                    27086752
                                    T{ value-info-state
                                        { class number }
                                        { interval
                                            full-interval
                                        }
                                    }
                                }
                                {
                                    27086747
                                    T{ value-info-state
                                        { class real }
                                        { interval
                                            T{ interval
                                                { from { 0 f } }
                                                { to
                                                    { 1/0. t }
                                                }
                                            }
                                        }
                                    }
                                }
                                {
                                    27086751
                                    T{ value-info-state
                                        { class number }
                                        { interval
                                            full-interval
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                {
                    T{ #shuffle
                        { mapping
                            {
                                { 27086753 27086743 }
                                { 27086754 27086743 }
                            }
                        }
                        { in-d V{ 27086743 } }
                        { out-d V{ 27086753 27086754 } }
                    }
                    T{ #call
                        { word abs }
                        { in-d V{ 27086754 } }
                        { out-d { 27086755 } }
                        { info
                            H{
                                {
                                    27086754
                                    T{ value-info-state
                                        { class real }
                                        { interval
                                            T{ interval
                                                { from
                                                    { -1/0. t }
                                                }
                                                { to { 0 t } }
                                            }
                                        }
                                    }
                                }
                                {
                                    27086755
                                    T{ value-info-state
                                        { class real }
                                        { interval
                                            T{ interval
                                                { from { 0 t } }
                                                { to
                                                    { 1/0. t }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                    T{ #push
                        { literal 100 }
                        { out-d { 27086756 } }
                    }
                    T{ #call
                        { word > }
                        { in-d V{ 27086755 27086756 } }
                        { out-d { 27086757 } }
                        { info
                            H{
                                {
                                    27086755
                                    T{ value-info-state
                                        { class real }
                                        { interval
                                            T{ interval
                                                { from { 0 t } }
                                                { to
                                                    { 1/0. t }
                                                }
                                            }
                                        }
                                    }
                                }
                                {
                                    27086756
                                    T{ value-info-state
                                        { class fixnum }
                                        { interval
                                            T{ interval
                                                { from
                                                    { 100 t }
                                                }
                                                { to { 100 t } }
                                            }
                                        }
                                        { literal 100 }
                                        { literal? t }
                                    }
                                }
                                {
                                    27086757
                                    T{ value-info-state
                                        { class object }
                                        { interval
                                            full-interval
                                        }
                                    }
                                }
                            }
                        }
                    }
                    T{ #if
                        { in-d { 27086757 } }
                        { children
                            {
                                {
                                    T{ #shuffle
                                        { mapping
                                            {
                                                {
                                                    27086758
                                                    27086753
                                                }
                                                {
                                                    27086759
                                                    27086753
                                                }
                                            }
                                        }
                                        { in-d V{ 27086753 } }
                                        { out-d
                                            V{
                                                27086758
                                                27086759
                                            }
                                        }
                                    }
                                    T{ #push
                                        { literal 2 }
                                        { out-d { 27086760 } }
                                    }
                                    T{ #call
                                        { word /i }
                                        { in-d
                                            V{
                                                27086759
                                                27086760
                                            }
                                        }
                                        { out-d { 27086761 } }
                                        { info
                                            H{
                                                {
                                                    27086760
                                                    T{
                                                    value-info-state
                                                        { class
                                                            fixnum
                                                        }
                                                        {
                                                        interval
                                                            T{
                                                            interval
                                                                {
                                                                from
                                                                    {
                                                                        2
                                                                        t
                                                                    }
                                                                }
                                                                {
                                                                to
                                                                    {
                                                                        2
                                                                        t
                                                                    }
                                                                }
                                                            }
                                                        }
                                                        {
                                                        literal
                                                            2
                                                        }
                                                        {
                                                        literal?
                                                            t
                                                        }
                                                    }
                                                }
                                                {
                                                    27086761
                                                    T{
                                                    value-info-state
                                                        { class
                                                            integer
                                                        }
                                                        {
                                                        interval
                                                            full-interval
                                                        }
                                                    }
                                                }
                                                {
                                                    27086759
                                                    T{
                                                    value-info-state
                                                        { class
                                                            real
                                                        }
                                                        {
                                                        interval
                                                            T{
                                                            interval
                                                                {
                                                                from
                                                                    {
                                                                        -1/0.
                                                                        t
                                                                    }
                                                                }
                                                                {
                                                                to
                                                                    {
                                                                        0
                                                                        t
                                                                    }
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                    T{ #call
                                        { word foo }
                                        { in-d V{ 27086761 } }
                                        { out-d { 27086762 } }
                                        { info
                                            H{
                                                {
                                                    27086761
                                                    T{
                                                    value-info-state
                                                        { class
                                                            integer
                                                        }
                                                        {
                                                        interval
                                                            full-interval
                                                        }
                                                    }
                                                }
                                                {
                                                    27086762
                                                    T{
                                                    value-info-state
                                                        { class
                                                            number
                                                        }
                                                        {
                                                        interval
                                                            full-interval
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                    T{ #call
                                        { word - }
                                        { in-d
                                            V{
                                                27086758
                                                27086762
                                            }
                                        }
                                        { out-d { 27086763 } }
                                        { info
                                            H{
                                                {
                                                    27086762
                                                    T{
                                                    value-info-state
                                                        { class
                                                            number
                                                        }
                                                        {
                                                        interval
                                                            full-interval
                                                        }
                                                    }
                                                }
                                                {
                                                    27086763
                                                    T{
                                                    value-info-state
                                                        { class
                                                            number
                                                        }
                                                        {
                                                        interval
                                                            full-interval
                                                        }
                                                    }
                                                }
                                                {
                                                    27086758
                                                    T{
                                                    value-info-state
                                                        { class
                                                            real
                                                        }
                                                        {
                                                        interval
                                                            T{
                                                            interval
                                                                {
                                                                from
                                                                    {
                                                                        -1/0.
                                                                        t
                                                                    }
                                                                }
                                                                {
                                                                to
                                                                    {
                                                                        0
                                                                        t
                                                                    }
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                                {
                                    T{ #shuffle
                                        { mapping { } }
                                        { in-d V{ 27086753 } }
                                        { out-d V{ } }
                                    }
                                    T{ #push
                                        { literal 42 }
                                        { out-d { 27086765 } }
                                    }
                                }
                            }
                        }
                        { live-branches { t t } }
                    }
                    T{ #phi
                        { phi-in-d
                            { { 27086770 } { 27086771 } }
                        }
                        { phi-info-d
                            {
                                {
                                    T{ value-info-state
                                        { class number }
                                        { interval
                                            full-interval
                                        }
                                    }
                                }
                                {
                                    T{ value-info-state
                                        { class fixnum }
                                        { interval
                                            T{ interval
                                                { from
                                                    { 42 t }
                                                }
                                                { to { 42 t } }
                                            }
                                        }
                                        { literal 42 }
                                        { literal? t }
                                    }
                                }
                            }
                        }
                        { out-d { 27086767 } }
                        { terminated { f f } }
                    }
                }
            }
        }
        { live-branches { t t } }
    }
    T{ #phi
        { phi-in-d { { 27086772 } { 27086773 } } }
        { phi-info-d
            {
                {
                    T{ value-info-state
                        { class number }
                        { interval full-interval }
                    }
                }
                {
                    T{ value-info-state
                        { class number }
                        { interval full-interval }
                    }
                }
            }
        }
        { out-d { 27086768 } }
        { terminated { f f } }
    }
    T{ #return
        { in-d V{ 27086768 } }
        { info
            H{
                {
                    27086768
                    T{ value-info-state
                        { class number }
                        { interval full-interval }
                    }
                }
            }
        }
    }
}

: foo-call ( -- node )
    4 foo-tree nth children>> first 3 swap nth ;

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
