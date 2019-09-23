! Copyright (C) 2008, 2010 Slava Pestov.
! See http://factorcode.org/license.txt for BSD license.
USING: accessors alien.c-types arrays assocs classes classes.algebra
classes.algebra.private classes.maybe classes.tuple.private combinators
combinators.short-circuit compiler.tree compiler.tree.builder
compiler.tree.optimizer compiler.tree.propagation.constraints
compiler.tree.propagation.info compiler.tree.propagation.inlining
compiler.tree.propagation.nodes compiler.tree.propagation.output-infos
compiler.tree.propagation.slots continuations formatting fry io kernel make math
generic
namespaces prettyprint sequences sets stack-checker.dependencies words ;
IN: compiler.tree.propagation.simple

SYMBOL: propagation-cache
! propagation-cache [ H{ } clone ] initialize ! Should only be needed during dev switch

M: #introduce propagate-before
    out-d>> [ object-info swap set-value-info ] each ;

M: #push propagate-before
    [ literal>> <literal-info> ] [ out-d>> first ] bi
    set-value-info ;

: refine-value-infos ( classes/f values -- )
    [ refine-value-info ] 2each ;

: set-value-infos ( infos values -- )
    [ set-value-info ] 2each ;

M: #declare propagate-before
    ! We need to force the caller word to recompile when the
    ! classes mentioned in the declaration are redefined, since
    ! now we're making assumptions about their definitions.
    declaration>> [
        [ add-depends-on-class ]
        [ <class-info> swap refine-value-info ]
        bi
    ] assoc-each ;

: predicate-constraints ( value class boolean-value -- constraint )
    [ [ is-instance-of ] dip t--> ]
    [ [ class-not is-instance-of ] dip f--> ]
    3bi 2array ;

: custom-constraints ( #call quot -- )
    [ [ in-d>> ] [ out-d>> ] bi append ] dip
    with-datastack first assume ;

: compute-constraints ( #call word -- )
    dup "constraints" word-prop [ nip custom-constraints ] [
        dup predicate? [
            [ [ in-d>> first ] [ out-d>> first ] bi ]
            [ "predicating" word-prop ] bi*
            swap predicate-constraints assume
        ] [ 2drop ] if
    ] if* ;

ERROR: invalid-outputs #call infos ;

: check-outputs ( #call infos -- infos )
    over out-d>> over [ length ] bi@ =
    [ nip ] [ invalid-outputs ] if ;

: call-outputs-quot ( #call word -- infos )
    dupd
    [ in-d>> [ value-info ] map ]
    [ "outputs" word-prop ] bi*
    with-datastack check-outputs ;

: literal-inputs? ( #call -- ? )
    in-d>> [ value-info literal?>> ] all? ;

: input-classes-match? ( #call word -- ? )
    [ in-d>> ] [ "input-classes" word-prop ] bi*
    [ [ value-info literal>> ] dip instance? ] 2all? ;

: foldable-call? ( #call word -- ? )
    {
        [ nip foldable? ]
        [ drop literal-inputs? ]
        [ input-classes-match? ]
    } 2&& ;

: (fold-call) ( #call word -- info )
    [ [ out-d>> ] [ in-d>> [ value-info literal>> ] map ] bi ] [ '[ _ execute ] ] bi*
    '[ _ _ with-datastack [ <literal-info> ] map nip ]
    [ drop length [ object-info ] replicate ]
    recover ;

: fold-call ( #call word -- )
    [ (fold-call) ] [ drop out-d>> ] 2bi set-value-infos ;

: predicate-output-infos/literal ( info class -- info )
    [ literal>> ] dip
    '[ _ _ instance? <literal-info> ]
    [ drop object-info ]
    recover ;

: predicate-output-infos/class ( info class -- info )
    [ class>> ] dip evaluate-class-predicate
    dup +incomparable+ eq? [ drop object-info ] [ <literal-info> ] if ;

: predicate-output-infos ( info class -- info )
    over literal?>>
    [ predicate-output-infos/literal ]
    [ predicate-output-infos/class ]
    if ;

: propagate-predicate ( #call word -- infos )
    [ in-d>> first value-info ]
    [ "predicating" word-prop ] bi*
    [ nip +conditional+ depends-on ]
    [ predicate-output-infos 1array ] 2bi ;

: default-output-value-infos ( #call word -- infos )
    "default-output-classes" word-prop
    [ class-infos ] [ out-d>> length object-info <repetition> ] ?if ;

: null-infos? ( infos -- ? )
    [ null-info = ] any? ;

: literal-infos? ( infos -- ? )
    [ literal?>> ] any? ;

! TODO: skip this stuff when no infos are given!
: check-consistent-effects ( #call infos -- ? )
    [ check-outputs ] [
        dup invalid-outputs? [
            2drop
           [  "FIXME: Inconsistent stack effect output for compiled word: " write
            word>> name>> print ] with-output>error
            f
        ] [ rethrow ] if
    ] recover
    ;

SYMBOL: propagate-output-infos?
propagate-output-infos? [ t ] initialize

! Force literal? to f to prevent non-specified inlining.  Class/Interval info is
! still propagated.
! This is quite verbose, mainly for catching things which indicate other problems.
: check-copy-output-infos ( #call word -- ? )
    "output-infos" word-prop
    {
        { [ propagate-output-infos? get not ] [ 2drop f ] }
        { [ dup not ] [ 2drop f ] }
        { [ 2dup check-consistent-effects not ] [ 2drop f ] }
        { [ [ word>> name>> ] dip dup null-infos? ]
          [ drop "WARNING: ignoring NULL infos from " prepend write nl f ] }
        ! { [ dup literal-infos? ]
        !   [ drop "WARNING: ignoring LITERAL infos from " prepend write nl f ] }
        [ 2drop t ]
    } cond
    ;

SYMBOL: custom-fallback-propagation-passes

! : prime-propagation-cache ( word -- )
!     propagation-cache get [ drop f ] cache drop
!     ;

! : cached-output-infos ( word -- info/f ? )
!     propagation-cache get at*
!     ;

! : update-propagation-cache ( word info -- info )
!     2dup "storing cached info for %s: %[%s, %]" printf nl
!     [ propagation-cache get set-at ] keep ;

! : (compute-output-infos) ( #call word -- infos )
!     dup prime-propagation-cache
!     dup "computing interim info for %s" printf nl
!     dup build-tree
!     custom-fallback-propagation-passes get
!     [ call( nodes -- nodes ) ]
!     [ optimize-tree ] if*
!     should-store-output-infos?
!     [ update-propagation-cache nip ]
!     [ default-output-value-infos ] if* ;

! : check-propagation-cycle ( call word cached-infos -- infos )
!     [ 2nip ]
!     [ dup "cycle detected for %s" printf nl
!       default-output-value-infos
!     ] if* ;

! : compute-output-infos ( call word -- info )
!     dup cached-output-infos
!     [ check-propagation-cycle ]
!     [ drop (compute-output-infos) ] if ;

: get-output-infos ( call word -- info )
    nip "output-infos" word-prop ;
    ! [
    !     propagation-cache get swapd [ "miss" print compute-output-infos ] with cache
    ! ] keep
    ! over "Using info for %s: %[%s, %]" printf nl
    ! compute-output-infos

! :: get-output-infos ( call word -- info )
!     word "output-infos" word-prop
!     [
!         prime-propagation-cache
!         word cached-output-infos :> ( infos found )
!         found
!         [ call word infos check-cached-output-infos ]
!         [ call word compute-output-infos ] if
!     ] unless*
!     ;

! Register conditional dependency here
: copy-output-infos ( #call word -- infos )
    ! [
        2dup check-copy-output-infos
        [ get-output-infos ]
        [ default-output-value-infos ] if
    ! ] keep
    ! over add-depends-on-output-infos
    ;

: output-value-infos ( #call word -- infos )
    {
        { [ dup \ <tuple-boa> eq? ] [ drop propagate-<tuple-boa> ] }
        { [ dup sequence-constructor? ] [ propagate-sequence-constructor ] }
        { [ dup predicate? ] [ propagate-predicate ] }
        { [ dup "outputs" word-prop ] [ call-outputs-quot ] }
        { [ dup "output-infos" word-prop ] [ copy-output-infos ] }
        [ default-output-value-infos ]
    } cond ;

M: #call propagate-before
    dup word>> {
        { [ 2dup foldable-call? ] [ fold-call ] }
        { [ 2dup do-inlining ] [
            [ output-value-infos ] [ drop out-d>> ] 2bi refine-value-infos
        ] }
        [
            [ [ output-value-infos ] [ drop out-d>> ] 2bi set-value-infos ]
            [ compute-constraints ]
            2bi
        ]
    } cond ;

M: #call annotate-node
    dup [ in-d>> ] [ out-d>> ] bi append (annotate-node) ;

: propagate-input-infos ( node infos/f -- )
    swap in-d>> refine-value-infos ;

! The method slot seems to have either a single word or a quotation
: add-output-value-dep ( call word -- )
    [ copy-output-infos ] keep
    ! dup  "%s, " printf
    swap
    add-depends-on-output-infos ;

: add-output-value-dependencies ( node -- )
    [ dup word>> add-output-value-dep ]
    [ dup method>> dup method? [ add-output-value-dep ] [ 2drop ] if ] bi
    ;

M: #call propagate-after
    [ dup word>> word>input-infos propagate-input-infos ]
    [ add-output-value-dependencies ] bi
    ! [ drop ] bi
    ;

: propagate-alien-invoke ( node -- )
    [ out-d>> ] [ params>> return>> ] bi
    [ drop ] [ c-type-class <class-info> swap first set-value-info ] if-void ;

M: #alien-node propagate-before propagate-alien-invoke ;

M: #alien-callback propagate-around child>> (propagate) ;

M: #return annotate-node dup in-d>> (annotate-node) ;
