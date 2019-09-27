USING: accessors arrays compiler.tree
compiler.tree.propagation.implicit-recursive.splice-nodes
compiler.tree.propagation.info kernel math math.intervals math.private sequences
tools.test typed ;
IN: compiler.tree.propagation.implicit-recursive.splice-nodes.tests

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

: test-call ( -- call )
    test-if children>> first third ;

: test-base-case-branch ( -- nodes )
    test-if children>> second ;

{ t } [ test-call test-if children>> first child-contains-node? ] unit-test
{ f } [ test-call test-if children>> second child-contains-node? ] unit-test


test-base-case-branch 1array [ test-call test-if reject-call* ] unit-test


! * Multiple Call Sites

: foo ( x -- x )
    { { [ dup 0 > ] [ dup 1 - foo - ] }
      { [ dup abs 100 > ] [ dup 2 /i foo - ] }
      [ drop 42 ]
    } cond ;
