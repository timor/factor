USING: accessors arrays assocs byte-arrays classes classes.algebra combinators
combinators.short-circuit compiler.messages compiler.tree
compiler.tree.builder.private compiler.tree.normalization
compiler.tree.propagation.info
compiler.tree.propagation.inline-propagation.cache
compiler.tree.propagation.inlining compiler.tree.propagation.nodes
compiler.tree.recursive compiler.utilities compiler.word-props continuations
effects fry generic generic.single hashtables kernel locals math namespaces
sequences sets stack-checker.dependencies stack-checker.errors strings words ;

IN: compiler.tree.propagation.inline-propagation
! Make sure that gets loaded!
USE: compiler.tree.propagation.inline-propagation.known-words
FROM: namespaces => set ;

UNION: primitive-sequence string byte-array array ;

ERROR: null-value-info ;
: assert-non-null-info ( value-info -- )
    null-info = [ null-value-info ] when ;

! : convex-input-info ( value-info -- value-info )
!     class>> <class-info> ;
!     ! dup assert-non-null-info
!     ! dup literal>>
!     ! { { [ dup primitive-sequence? ] [ drop [ slots>> first ] [ class>> ] bi <sequence-info> ] }
!     !   { [ dup tuple? ] [ drop [ slots>> ] [ class>> ] bi <tuple-info> ] }
!     !   [ drop [ class>> ] [ interval>> ] bi <class/interval-info> ] } cond
!     ! ! dup { [ interval>> special-interval? not ]
!     ! !       [ literal>> identity-tuple? ]
!     ! !       [ literal>> { [ word? ] [ name>> "( gensym )" = ] } 1&& ]
!     ! !       [ literal>> quotation? ]
!     ! !       [ literal>> { [ primitive-sequence? ] [ empty? not ] } 1&& ]
!     ! ! } 1||
!     ! ! [ class>> <class-info> ] when
!     ! dup slots>> [
!     !     ! [ clone ] dip
!     !     [ dup [ convex-input-info ] when ] map
!     !     >>slots
!     ! ] when*
!     ! ! dup assert-non-null-info
!     ! ;

!     ! dup interval>> special-interval?
!     ! [ class>> <class-info> ] unless
!     ! dup slots>> [
!     !     [ clone ] dip
!     !     [ dup [ convex-input-info ] when ] map
!     !     >>slots
!     ! ] when* ;
!     ! ! dup literal?>> [ class>> <class-info> ] when ;

TUPLE: inline-signature { class maybe{ classoid } read-only } { slots array read-only } ;
CONSTANT: object-signature T{ inline-signature f object }
! Limit nesting of signatures which would result in inline propagation loops
CONSTANT: max-signature-depth 10
! CONSTANT: max-signature-depth 5

: (info>signature) ( depth info/f -- sig/f )
    dup
    [
        [ 1 + ] dip over max-signature-depth >
        [ 2drop object-signature ]
        [ swap [ class>> ] [ slots>> [ (info>signature) ] with { } map-as ] with bi inline-signature boa ] if
    ]
    [ nip ] if ;


: info>signature ( info/f -- sig/f ) 0 swap (info>signature) ;

: call-inline-signature ( #call -- obj )
    in-d>> [ value-info info>signature ] { } map-as ;

: signature>info ( sig/f -- info/f )
    dup
    [ [ class>> dup class-interval <class/interval-info> ] [ slots>> [ signature>info ] { } map-as ] bi >>slots ]
    when ;

: signatures>classes ( seq -- seq )
    sift
    [ [ slots>> signatures>classes sift ] [ class>> ] bi prefix ]
    map concat ;

: value-info-classes ( infos -- classes/f )
    ! dup [ null-info = ] any?    ! This happens if inline propagation resulted in termination
    f
    [ drop f ] [ [ class>> ] map ] if ;
    ! swap word>> foldable? [ [ class>> <class-info> ] map ] unless ;
    ! [ [ f >>literal? f >>literal? ] map ] unless ;


ERROR: no-inline-class #call ;

! Make the nodes for propagation, prefix it with a #copy
:: inline-propagation-body ( #call -- nodes/f )
    #call [ [ in-d>> ] [ word>> ] bi
      build-tree-with ] curry [ inference-error? ] ignore-error/f
    dup
    { [ length 2 < ] [ penultimate #terminate? ] } 1||
    [ drop f ] [
        ! #call in-d>> dup length [ <value> ] replicate swap <#copy> prefix
        analyze-recursive normalize
    ] if ;

! Could be evil:
! : cached-inline-propagation-body ( #call -- nodes/f )
!     [ word>> ] keep over "inline-body" word-prop
!     [ 2nip ]
!     [ inline-propagation-body [ "inline-body" set-word-prop ] keep ] if* ;

! : deliteralize-info ( info -- info' )
!     clone f >>literal f >>literal?
!     dup class>> class-interval >>interval
!     [ [ dup [ deliteralize-info ] when ] map ] change-slots ;

:: propagate-body-for-infos ( #call signatures -- infos/f )
    ! #call in-d>> [ value-info deliteralize-info ] map :> input-info
    signatures [ signature>info ] map :> input-info
    ! #call word>> input-info "--- Using infos to propagate %u: %u" 3 format-compiler-message
    ! input-classes [ <class-info> ] map :> input-info
    #call inline-propagation-body
    [
        value-infos [ H{ } clone suffix ] change
        input-info #call in-d>> [ set-value-info ] 2each
        [ (propagate) ] keep last in-d>> [ value-info ] { } map-as
    ] [ f ] if* ;

:: splicing-classes ( #call signatures -- classes/f )
    ! #call word>> name>> signatures "--- Propagating nodes for infos: %u inputs: %u " 4 format-compiler-message
    #call word>> name>> signatures "--- Propagating non-inlined-word inline: %s %u" 3 format-compiler-message
    #call signatures propagate-body-for-infos
    value-info-classes dup :> res
    [
        ! #call signatures res record-inline-propagation
    ] [ f ] if* ;

! : trace-non-trivial-infos ( infos -- )
!     dup trivial-infos? not [ "--- Using inline-propagated infos %u" 3 format-compiler-message ] [ drop ] if ;

ERROR: maximum-inline-propagation-depth ;
! For debugging inline propagation loops
SYMBOL: inline-propagation-depth
inline-propagation-depth [ 0 ] initialize
: detect-infinite-recursion ( -- )
    inline-propagation-depth get 100 >=
    [ maximum-inline-propagation-depth ] when ;

! * Dependency tracking
! During inline propagation, we save a reference to the original dependency
! variables in the stack variable, where we store the definition dependencies on
! the inlined calls only.  Then, after
SYMBOL: current-inline-dependencies

! : link-dependencies-old ( -- )
!     dependencies-stack [ get-dependencies-namespace suffix ] change
!     H{ } clone dependencies namespaces:set
!     H{ } clone generic-dependencies namespaces:set
!     HS{ } clone conditional-dependencies namespaces:set ;

! : link-dependencies-also-old ( word -- )
!     inline-propagation-dependencies get [ drop H{ } clone ] cache
!     dependencies over [ drop H{ } clone ] cache dependencies set
!     generic-dependencies over [ drop H{ } clone ] cache generic-dependencies set
!     conditional-dependencies over [ drop HS{ } clone ] cache conditional-dependencies set
!     drop ;

: inline-top-level? ( -- x )
    inline-propagation-depth get 0 = ; inline

: make-dependencies-namespace ( -- hashtable )
    H{ } clone dependencies associate
    H{ } clone generic-dependencies pick set-at
    HS{ } clone conditional-dependencies pick set-at ;

: link-inline-dependencies ( -- )
    inline-top-level?
    [
        make-dependencies-namespace
        current-inline-dependencies set
    ] when
    ;

: with-inline-dependencies ( quot -- )
    inline-top-level? f current-inline-dependencies get ?
    swap with-variables ; inline

: trivial-classes? ( classes -- ? )
    [ object class= ] all? ;

! We record the additional dependencies in the current-inline-dependencies variable.
: record-inline-propagation ( #call signature -- )
    ! dependencies-stack get ?first
    ! [
        signatures>classes members [ dup object = [ drop ] [ add-depends-on-class ] if ] each
        ! copied record-inlining code from cleanup here due to vocab dependencies
        dup method>>
        [ dup class>> [ no-inline-class ] unless
          dup method>> word? [
              [ [ class>> ] [ word>> ] bi add-depends-on-generic ] [
                  [ class>> ] [ word>> ] [ method>> ] tri
                  add-depends-on-method
              ] bi
          ] [ drop ] if  ] [ word>> +definition+ depends-on ]
        if ;
    ! ] with-inline-dependencies ;

! TODO: check whether we get a recursion problem here with self-dependencies.
! If we are at the top-level, include the dependencies in the regular variables
! If we are doing nested propagation, copy the dependencies to the current
! inline-deps "accumulator" instead
: copy-dependencies ( namespace -- )
    [ dependencies of [ depends-on ] assoc-each ]
    [ generic-dependencies of [ swap add-depends-on-generic ] assoc-each ]
    [ conditional-dependencies of conditional-dependencies get
      [ swap union! drop ] [ drop ] if*
    ] tri ;

: include-inline-dependencies ( entry -- )
    ! inline-propagation-depth get 1 = f current-inline-dependencies get ?
    ! current-inline-dependencies get
    [
        dependencies>>
        copy-dependencies
    ] with-inline-dependencies ;

! * Recursion tracking
SINGLETON: +inline-recursion+
SYMBOL: signature-trace

ERROR: inline-propagation-recursion word sig ;

: cache-at-unless-recursion ( classes/f sig info-cache -- cache-entry )
    2dup at dup dup [ classes>> ] when +inline-recursion+?
    [ [ 3drop ] dip ]
    [ drop [ current-inline-dependencies get clone [ clone ] assoc-map <inline-propagation-entry> ] 2dip [ set-at ] keepdd ] if ;

SYMBOL: inline-trace
: make-scope ( word sig -- recursion? )
    2array dup inline-trace get key?
    [ drop t ]
    [ make-dependencies-namespace 2array inline-trace [ swap suffix ] change f ] if ;

: with-inline-trace ( ..a word sig quot: ( ..a -- ..b classes ) -- ..b classes/f namespace/recursion )
    '[ _ _
        make-scope
        [ f +inline-recursion+ ]
        [
            dependencies off
            conditional-dependencies off
            generic-dependencies off
            _ call
            inline-trace get last second
        ] if
    ] with-scope ; inline

: with-current-deps ( quot -- )
    inline-trace get ?last [ second ] [ f ] if*
    swap with-variables ; inline

:: compute-inline-propagation-classes ( #call word sig -- classes dependencies )
    word sig
    [
        #call sig splicing-classes
    ] with-inline-trace ;

:: cached-inline-propagation-classes ( #call word -- classes )
    word inline-info-cache get [ drop H{ } clone ] cache :> info-cache
    #call call-inline-signature dup :> sig info-cache [
        [ #call word ] dip compute-inline-propagation-classes
        <inline-propagation-entry> ] cache
    [ classes>> ] [ dependencies>> ] bi :> ( classes deps )
    { [ classes trivial-classes? ] [ deps +inline-recursion+? ] } 0||
    [ f ]
    [ word sig classes "--- classes of %u with %u: %u" 4 format-compiler-message
      [ #call sig record-inline-propagation
        deps copy-dependencies ] with-current-deps
      classes
    ] if ;

! * TODO Dispatch Inlining
: call-dispatch-classoid ( #call generic -- classoid )
    [ dispatch# ] [ in-d>> <reversed> ] bi* nth
    value-info class>> ;

! : dispatch-useful? ( #call generic -- ? )
!     dup standard-generic? [ 2drop f ]
!     [
!         [ call-dispatch-classoid ] [ "methods" word-prop ] bi
!         [ first ] map <anonymous-union> class<=
!     ] if ;

! When trying really hard to propagate dispatch, compile in the actual dispatch for propagation
: make-executer ( method -- quot )
    dup stack-effect [ execute-effect ] 2curry ;

: dispatch-inlining-quot ( classoid word -- quot )
    [ "methods" word-prop
      [ keys [ classes-intersect? ] with filter ] [ extract-keys ] bi
      sort-methods <reversed> class-predicates [ make-executer ] assoc-map
    ] keep
    "default-method" word-prop dup word? [ make-executer ] when suffix
    [ cond ] curry ;

! NOTE: We don't propagate through generic dispatches.  An optimization could be
! to determine whether the input is a proper subset of the generic's method
! definers, and to inline-propagate all of those and return the union info
: inline-propagation-classes ( #call word -- classes/f )
    2dup  { [ nip primitive? ]
            [ nip generic? ]
            [ nip never-inline-word? ]
            [ nip no-compile? ]
            [ nip custom-inlining? ]
            [ drop out-d>> empty? ]
            [ nip "never-propagate-inline" word-prop ] } 2||
    [ 2drop f ]
    [
        cached-inline-propagation-classes
      dup +inline-recursion+? [ drop f ] when
    ] if
    ! dup trace-non-trivial-infos
    ;
