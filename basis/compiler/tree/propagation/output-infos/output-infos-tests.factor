USING: accessors assocs combinators compiler compiler.tree.propagation.info
compiler.tree.propagation.inlining
compiler.tree.propagation.mutually-recursive.interface compiler.units kernel
kernel.private math math.intervals math.order namespaces sequences tools.test
words ;
IN: compiler.tree.propagation.output-infos.tests

! TODO: insert missing unit test!


! * Nested Compilation

: with-opt ( quot -- )
    H{ { propagate-recursive? t }
       { nested-compilation? t } } swap with-variables ; inline

: with-watched-words ( words quot -- )
    {
        ! [ drop [ reset ] each ]
        ! [ drop [ watch ] each ]
        [ nip call ]
        ! [ drop [ reset ] each ]
    } 2cleave
    ; inline

: test-output-infos ( words -- infos )
    [
        { compile-word maybe-compile-word nested-compile inline-nested-compilation inline-recursive-call }
        [ recompile ] with-watched-words
        drop ]
    [ [ dup "output-infos" word-prop ] map>alist ] bi ;

: fun1 ( x -- y ) { fixnum } declare 3 + ;

: fun2 ( x -- y ) fun1 ;

{ } [ { fun1 fun2 } recompile drop ] unit-test

{ t } [ { fun2 fun1 } test-output-infos values first first object-info = ] unit-test

{ integer } [ { fun1 fun2 } test-output-infos values second first class>> ] unit-test

{ } [ nested-compilation? [ { fun1 fun2 } recompile drop ] with-variable-on ] unit-test

{ integer } [ nested-compilation?
              [ { fun2 fun1 } test-output-infos values first first class>> ]
            with-variable-on ] unit-test

! Single Recursion
: fun4 ( x -- y )
    dup 0 > [ 1 - fun4 ] [ drop 42 ] if ;

! Brute-force prove that interval inference is not too optimistic
:: check1 ( word -- ? )
    [ word 1array test-output-infos values first first interval>> ] with-opt
    1000 <iota> [ 500 - word execute( x -- x ) ] map minmax [a,b] swap interval-subset?
    ;

! Should work with compiler.tree.propagation.mutually-recursive:
{ 42 } [ propagate-recursive? [ { fun4 } test-output-infos values first first literal>> ] with-variable-on ] unit-test

! [ nested-compilation? [ { fun4 } recompile drop ] with-variable-on ] [ nested-compilation-cycle? ] must-fail-with
! After Error Handling:
{ t } [ nested-compilation? [ { fun4 } test-output-infos values first first object-info = ]
        with-variable-on ] unit-test

! Should refine inlining result with object-info
{ 42 } [ H{ { propagate-recursive? t }
            { nested-compilation?  t } }
         [ { fun4 } test-output-infos values first first literal>> ] with-variables ] unit-test

{ t } [ \ fun4 check1 ] unit-test

: fun41 ( x -- y )
    abs dup 10 < [ 5 + ] [ 2 /i fun41 ] if ;

{ t } [ \ fun41 check1 ] unit-test

: fun42 ( x -- y )
    0 42 clamp
    dup 5 > [ 0 21 clamp 1 - fun42 ] [ 2 + ] if ;

{ t } [ \ fun42 check1 ] unit-test


! Mutual dependencies
DEFER: fun6
: fun5 ( x -- y )
    dup 0 > [ 1 - fun6 ] [ drop 42 ] if ;
: fun6 ( x -- y )
    dup 0 > [ 1 - fun5 ] [ drop 69 ] if ;

! [ nested-compilation? [ { fun5 fun6 } recompile drop ] with-variable-on ] [ nested-compilation-cycle? ] must-fail-with
! After Error Handling:
{ t } [ nested-compilation? [ { fun5 } test-output-infos values first first object-info = ] with-variable-on ] unit-test
{ t } [ nested-compilation? [ { fun6 } test-output-infos values first first object-info = ] with-variable-on ] unit-test


! Nested compilation with recursive propagation should be able to resolve this
{ fixnum } [ H{ { propagate-recursive? t }
                { nested-compilation?  t } }
             [ { fun6 fun5 } test-output-infos values first first  class>> ] with-variables ] unit-test

: info-interval-points ( info -- lower upper )
    interval>> interval>points [ first ] bi@ ;

{ 42 69 } [ [ { fun6 fun5 } test-output-infos values first first info-interval-points ] with-opt ] unit-test

! Diverging value info tests

! Non-tail-recursive operations
: fun70 ( x -- y )
    0 26 clamp
    dup 5 > [ 1 - fun70 7 + ] when ;

{ t } [ \ fun70 check1 ] unit-test

: fun7 ( x -- y )
    0 26 clamp
    dup 13 rem 0 =
    [ 4 + ] [ 1 + fun7 5 + ] if ;

{ t } [ \ fun7 check1 ] unit-test

{ 4 1/0. } [ [ { fun7 } test-output-infos values first first info-interval-points ] with-opt ] unit-test

! Both call sites cause growth
: fun71 ( x -- y )
    0 26 clamp
    dup 5 > [ dup 10 > [ 1 - fun71 3 + ] [ 1 - fun71 4 + ] if ] when
    ;

{ t } [ \ fun71 check1 ] unit-test

{ 0 1/0. } [ [ { fun71 } test-output-infos values first first info-interval-points ] with-opt ] unit-test

! Operations after branch return

! Both call sites cause growth, but final subtraction compensates it.
: fun72 ( x -- y )
    0 26 clamp
    dup 5 > [ dup 10 > [ 1 - fun72 3 + ] [ 1 - fun72 4 + ] if ] when
    3 -
    ;

{ t } [ \ fun72 check1 ] unit-test

{ -3 24 }
[ [ { fun72 } test-output-infos values first first info-interval-points ] with-opt ] unit-test

! Operations after final phi node which cause growth, but clamping can not be detected.
: fun8 ( x -- y )
    -1 26 clamp
    dup 0 >
    [ 5 - fun8 ] when
    4 + ;

{ t } [ \ fun8 check1 ] unit-test

! { 3 34 }
{ 3 1/0. }
[ [ { fun8 } test-output-infos values first first info-interval-points ] with-opt ] unit-test

! Same thing, but without branch constraint
: fun8a ( x -- y )
    -1 26 clamp
    dup even?
    [ 5 - fun8a ] when
    4 + ;

{ t } [ \ fun8a check1 ] unit-test

! { 3 34 }
{ 3 1/0. }
[ [ { fun8a } test-output-infos values first first info-interval-points ] with-opt ] unit-test

! Same, but enough to diverge:
: fun9 ( x -- y )
    0 26 clamp
    dup 0 >
    [ 5 - fun9 ] when
    6 + ;

{ t } [ \ fun9 check1 ] unit-test

{ 6 1/0. } [ [ { fun9 } test-output-infos values first first info-interval-points ] with-opt ] unit-test


! * Mutual recursion inlining (unused?)

CONSTANT: fun5-tree
{
    T{ #introduce { out-d { 10928520 } } }
    T{ #shuffle
        { mapping
            { { 10928511 10928520 } { 10928512 10928520 } }
        }
        { in-d V{ 10928520 } }
        { out-d V{ 10928511 10928512 } }
    }
    T{ #push { literal 0 } { out-d { 10928513 } } }
    T{ #call
        { word > }
        { in-d V{ 10928512 10928513 } }
        { out-d { 10928514 } }
        { info
            H{
                {
                    10928512
                    T{ value-info-state
                        { class object }
                        { interval full-interval }
                    }
                }
                {
                    10928513
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
                    10928514
                    T{ value-info-state
                        { class object }
                        { interval full-interval }
                    }
                }
            }
        }
    }
    T{ #if
        { in-d { 10928514 } }
        { children
            {
                {
                    T{ #push
                        { literal 1 }
                        { out-d { 10928515 } }
                    }
                    T{ #call
                        { word - }
                        { in-d V{ 10928511 10928515 } }
                        { out-d { 10928516 } }
                        { info
                            H{
                                {
                                    10928515
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
                                    10928516
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
                                    10928511
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
                            }
                        }
                    }
                    T{ #call
                        { word fun6 }
                        { in-d V{ 10928516 } }
                        { out-d { 10928517 } }
                        { info
                            H{
                                {
                                    10928516
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
                                    10928517
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
                    T{ #shuffle
                        { mapping { { 10928521 10928517 } } }
                        { in-d { 10928517 } }
                        { out-d { 10928521 } }
                    }
                }
                {
                    T{ #shuffle
                        { mapping { } }
                        { in-d V{ 10928511 } }
                        { out-d V{ } }
                    }
                    T{ #push
                        { literal 42 }
                        { out-d { 10928518 } }
                    }
                    T{ #shuffle
                        { mapping { { 10928522 10928518 } } }
                        { in-d { 10928518 } }
                        { out-d { 10928522 } }
                    }
                }
            }
        }
        { live-branches { t t } }
    }
    T{ #phi
        { phi-in-d { { 10928521 } { 10928522 } } }
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
        { out-d { 10928519 } }
        { terminated { f f } }
    }
    T{ #return
        { in-d V{ 10928519 } }
        { info
            H{
                {
                    10928519
                    T{ value-info-state
                        { class object }
                        { interval full-interval }
                    }
                }
            }
        }
    }
}

: fun5-if ( -- #if )
    4 fun5-tree nth ;

: fun5-call ( -- #call )
    fun5-if children>> first third ;
