! Copyright (C) 2008, 2010 Slava Pestov.
! See http://factorcode.org/license.txt for BSD license.
USING: accessors classes.algebra combinators compiler.tree
compiler.tree.combinators compiler.tree.propagation.constraints
compiler.tree.propagation.copy compiler.tree.propagation.info
compiler.tree.propagation.nodes compiler.tree.propagation.simple
kernel locals math math.intervals namespaces sequences ;
FROM: sequences.private => array-capacity ;
IN: compiler.tree.propagation.recursive

! For #call-recursive: infos1: latest-input-infos ( in-d in value-infos ),
! infos2: recursive-phi-infos ( out-d in infos>> of #enter-recursive  )
: check-fixed-point ( node infos1 infos2 -- )
    [ value-info<= ] 2all?
    [ drop ] [ label>> f >>fixed-point drop ] if ;

: latest-input-infos ( node -- infos )
    in-d>> [ value-info ] map ;

! Pulls up info from all call sites to set up comparison with the
! beginning-of-iteration stack state, which is stored on the input infos of the
! #enter-recursive loop header.
: recursive-stacks ( #enter-recursive -- stacks initial )
    [ label>> calls>> [ node>> node-input-infos ] map flip ]
    [ latest-input-infos ] bi ;

: counter-class ( interval class -- class' )
    dup fixnum class<= rot array-capacity-interval interval-subset? and
    [ drop array-capacity ] when ;

:: generalize-counter-interval ( interval initial-interval class -- interval' )
    interval class counter-class :> class
    {
        { [ interval initial-interval interval-subset? ] [ initial-interval ] }
        { [ interval empty-interval? ] [ initial-interval ] }
        {
            [ interval initial-interval interval>= t eq? ]
            [ class max-value [a,a] initial-interval interval-union ]
        }
        {
            [ interval initial-interval interval<= t eq? ]
            [ class min-value [a,a] initial-interval interval-union ]
        }
        [ class class-interval ]
    } cond ;

! NOTE: This code would actually modify the info state of the lazy value.
! Doesn't seem to be the right thing to do though.
! DEFER: generalize-counter
! : generalize-lazy-counter ( slot-info' lazy-initial -- )
!     break
!     [ lazy-info>info generalize-counter ]
!     [ values>> [ set-value-info ] with each  ] bi ;

! ! In case we are modifying tuples with lazy slots, we need to generalize the virtuals
! : generalize-counter-slot ( slot-info' initial -- slot-info )
!     dup lazy-info? [
!         [ generalize-lazy-counter ] keep
!     ] [
!         generalize-counter
!     ] if ;

: generalize-counter ( info' initial -- info )
    2dup [ not ] either? [ drop ] [
        2dup [ class>> null-class? ] either? [ drop ] [
            [ clone ] dip
            [
                [ drop ] [
                    [ [ interval>> ] bi@ ] [ drop class>> ] 2bi
                    generalize-counter-interval
                ] 2bi >>interval
            ]
            [ [ drop ] [ [ slots>> ] bi@ [ generalize-counter ] 2map ] 2bi >>slots ]
            bi
        ] if
    ] if ;

! Takes the recursive call site stack states and the iteration beginning state.
! The call-site states are all merged into a single virtual call site, and then
! extended using the entry state.  The result of that is then stored in the loop
! header out-d value info states and at the out-d infos of the header node.
: unify-recursive-stacks ( stacks initial -- infos )
    over empty? [ nip ] [
        [
            [ value-infos-union ] dip
            [ generalize-counter ] keep
            value-info-union
        ] 2map
    ] if ;

: propagate-recursive-phi ( #enter-recursive -- )
    [ recursive-stacks unify-recursive-stacks ] keep
    out-d>> set-value-infos ;

SYMBOL: sentinel
M: #recursive propagate-around ( #recursive -- )
    0 sentinel set-global
    constraints [ H{ } clone suffix ] change
    [
        bake-lazy-infos on
        sentinel counter 100 > [ "recursion limit" throw ] when
        constraints [ but-last H{ } clone suffix ] change

        child>>
        [ first compute-copy-equiv ]
        [ first propagate-recursive-phi ]
        [ (propagate) ]
        tri
    ] until-fixed-point ;

: recursive-phi-infos ( node -- infos )
    label>> enter-recursive>> node-output-infos ;

: generalize-return-interval ( info -- info' )
    dup [ literal?>> ] [ class>> null-class? ] bi or
    [ clone dup class>> class-interval >>interval ] unless ;

: generalize-return ( infos -- infos' )
    [ generalize-return-interval ] map ;

: return-infos ( node -- infos )
    label>> return>> node-input-infos generalize-return ;

: save-return-infos ( node infos -- )
    swap out-d>> set-value-infos ;

: unless-loop ( node quot -- )
    [ dup label>> loop?>> [ drop ] ] dip if ; inline

M: #call-recursive propagate-before ( #call-recursive -- )
    [
        [ ] [ latest-input-infos ] [ recursive-phi-infos ] tri
        check-fixed-point
    ]
    [
        [
            [ ] [ return-infos ] [ node-output-infos ] tri
            [ check-fixed-point ] [ drop save-return-infos ] 3bi
        ] unless-loop
    ] bi ;

M: #call-recursive annotate-node
    dup [ in-d>> ] [ out-d>> ] bi append (annotate-node) ;

M: #enter-recursive annotate-node
    dup out-d>> (annotate-node) ;

M: #return-recursive propagate-before ( #return-recursive -- )
    [
        [ ] [ latest-input-infos ] [ node-input-infos ] tri
        check-fixed-point
    ] unless-loop ;

M: #return-recursive annotate-node
    dup in-d>> (annotate-node) ;
