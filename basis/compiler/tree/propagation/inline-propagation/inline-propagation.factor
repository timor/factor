USING: accessors arrays assocs byte-arrays classes classes.algebra combinators
combinators.short-circuit compiler.messages compiler.tree
compiler.tree.builder.private compiler.tree.normalization
compiler.tree.propagation.info
compiler.word-props
compiler.tree.propagation.inline-propagation.cache
compiler.tree.propagation.inlining compiler.tree.propagation.nodes
compiler.tree.recursive compiler.utilities continuations effects generic
generic.hook generic.math generic.single kernel locals math namespaces sequences
stack-checker.dependencies stack-checker.errors strings words ;

IN: compiler.tree.propagation.inline-propagation
! Make sure that gets loaded!
USE: compiler.tree.propagation.inline-propagation.known-words

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
    #call word>> name>> "--- Propagating non-inlined-word inline: %s" 3 format-compiler-message
    #call signatures propagate-body-for-infos
    value-info-classes dup :> res
    [
        ! #call signatures res record-inline-propagation
    ] [ f ] if* ;

! : trace-non-trivial-infos ( infos -- )
!     dup trivial-infos? not [ "--- Using inline-propagated infos %u" 3 format-compiler-message ] [ drop ] if ;

SINGLETON: +inline-recursion+
SYMBOL: signature-trace

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

: link-inline-dependencies ( -- )
    inline-top-level?
    [ H{ } clone dependencies associate
      H{ } clone generic-dependencies pick set-at
      HS{ } clone conditional-dependencies pick set-at
      current-inline-dependencies set
      dependencies off
      generic-dependencies off
      conditional-dependencies off
    ] when ;
    ! dependencies over [ drop H{ } clone ] cache dependencies set
    ! generic-dependencies over [ drop H{ } clone ] cache generic-dependencies set
    ! conditional-dependencies over [ drop HS{ } clone ] cache conditional-dependencies set
    ! drop ;

! : cache-current-dependencies ( word -- )
!     inline-top-level?
!     [ current-inline-dependencies get inline-propagation-dependencies get set-at ]
!     [ drop ] if ;

: with-inline-dependencies ( assoc quot -- )
    current-inline-dependencies get swap with-variables ; inline

! : with-linked-dependencies-old ( word quot -- )
!     '[ _ link-inline-dependencies @ ] with-scope ; inline

! : with-linked-dependencies ( quot -- )
!     '[ _ link-inline-dependencies @ ] with-scope ; inline

! TODO: check whether we get a recursion problem here with self-dependencies.
! If we are at the top-level, include the dependencies in the regular variables
! If we are doing nested propagation, copy the dependencies to the current
! inline-deps "accumulator" instead
: include-inline-dependencies ( entry -- )
    inline-top-level? f current-inline-dependencies get ?
    [
        dependencies>>
        [ dependencies of [ depends-on ] assoc-each ]
        [ generic-dependencies of [ swap add-depends-on-generic ] assoc-each ]
        [ conditional-dependencies of conditional-dependencies get
          [ swap union! drop ] [ drop ] if*
        ] tri
    ] with-variables ;

: trivial-classes? ( classes -- ? )
    [ object class= ] all? ;

! We record the additional dependencies in the current-inline-dependencies variable.
: record-inline-propagation ( #call signature -- )
    ! dependencies-stack get ?first
    [
        signatures>classes members [ add-depends-on-class ] each
        ! copied record-inlining code from cleanup here due to vocab dependencies
        dup method>>
        [ dup class>> [ no-inline-class ] unless
          dup method>> word? [
              [ [ class>> ] [ word>> ] bi add-depends-on-generic ] [
                  [ class>> ] [ word>> ] [ method>> ] tri
                  add-depends-on-method
              ] bi
          ] [ drop ] if  ] [ word>> +definition+ depends-on ]
        if
    ] with-inline-dependencies ;

:: cached-inline-propagation-infos ( #call word -- classes/f )
    word { [ "no-compile" word-prop ] } 1&& [ "nope" throw ] when
    #call call-inline-signature :> sig
    word inline-info-cache get [ drop H{ } clone ] cache :> info-cache
    sig info-cache at*
    [
        word over classes>> "--- inline info cache hit for %u: %u " 5 format-compiler-message
    ]
    [
        [
            link-inline-dependencies
            inline-propagation-depth inc
            detect-infinite-recursion
            ! link-dependencies-old
            ! word link-inline-dependencies
            word sig 2array signature-trace get member?
            [ drop
              signature-trace get word sig 2array "--- Inline Propagation recursion: %u %u" 4 format-compiler-message
              +inline-recursion+ ]
            [ drop signature-trace [ word sig 2array suffix ] change
              #call sig splicing-classes ] if
            current-inline-dependencies get <inline-propagation-entry> :> entry
            entry sig info-cache set-at
            ! classes current-inline-dependencies get sig info-cache set-at :> classes
            #call word>> sig entry classes>> "--- inline classes: %u %u %u" 4 format-compiler-message
            ! entry ! classes +inline-recursion+?
            ! #call sig record-inline-propagation ] unless
            entry
        ] with-scope
    ] if
    [ include-inline-dependencies ]
    [ classes>> ] bi
    dup { [ +inline-recursion+? ] [ trivial-classes? ] } 1|| [ #call sig record-inline-propagation ] unless
    ;

! * Dispatch Inlining
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
: inline-propagation-infos ( #call word -- classes/f )
    2dup  { [ nip primitive? ]
            [ nip generic? ]
            [ nip never-inline-word? ]
            [ nip no-compile? ]
            [ nip custom-inlining? ]
            [ drop out-d>> empty? ]
            [ nip "never-propagate-inline" word-prop ] } 2||
    [ 2drop f ]
    [ cached-inline-propagation-infos
      dup +inline-recursion+? [ drop f ] when
    ] if
    ! dup trace-non-trivial-infos
    ;

! This needs to be done to all words in a compilation unit that are recompiled together.
! : reset-inline-info-cache ( word -- )
!     [ subwords ] keep suffix
!     [ [ "inline-propagation-infos" remove-word-prop ]
!       [ "inline-body" remove-word-prop ] bi ] each  ;
