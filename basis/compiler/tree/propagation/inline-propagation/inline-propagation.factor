USING: accessors arrays assocs byte-arrays combinators.short-circuit
compiler.messages compiler.tree compiler.tree.builder.private
compiler.tree.normalization compiler.tree.propagation.info
compiler.tree.propagation.inlining compiler.tree.propagation.nodes
compiler.tree.cleanup
compiler.tree.recursive compiler.utilities continuations formatting generic
generic.single generic.math
kernel locals math namespaces sequences stack-checker.dependencies
stack-checker.errors strings words ;

IN: compiler.tree.propagation.inline-propagation

! DOING: not annotating words, also only use classes

! An assoc storing cached inlined-infos for different value-info inputs for each word
SYMBOL: inline-info-cache
inline-info-cache [ H{ } clone ] initialize

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

: inline-signature ( #call -- obj )
    in-d>> [ value-info class>> ] { } map-as ;

: deliteralize-infos ( infos -- classes )
    [ class>> ] map ;
    ! swap word>> foldable? [ [ class>> <class-info> ] map ] unless ;
    ! [ [ f >>literal? f >>literal? ] map ] unless ;

: trivial-infos? ( infos -- ? )
    [ { [ object-info = ] [ class>> union{ t POSTPONE: f } = ] } 1|| ] all? ;

! : record-inline-propagation ( #call infos -- )
!     trivial-infos? [ drop ] [ word>> +definition+ depends-on ] if ;


! Note that we only record this on the top-level, which might be wrong if the
! parent of a nested specialization is not recompiled when the nested
! specialization changes...
:: record-inline-propagation ( #call input-classes output-classes -- )
    input-classes output-classes [ [ add-depends-on-class ] each ] bi@
    #call word>> :> word
    word method?
    [ word parent-word :> generic
      generic math-generic?
      [ number ] [ generic dispatch# input-classes nth ] if :> class
      class generic add-depends-on-generic
      class generic word add-depends-on-method
      ]
    [ word +definition+ depends-on ]
    if ;
    ! dup method? [ record-inline-method-propagation ] [ +definition+ depends-on ] if ;


SINGLETON: +inline-recursion+
SYMBOL: signature-trace

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

:: propagate-body-for-infos ( #call input-classes -- infos/f )
    input-classes [ <class-info> ] map :> input-info
    #call inline-propagation-body
    [ [
            value-infos [ H{ } clone suffix ] change
            input-info #call in-d>> [ set-value-info ] 2each
            [ (propagate) ] keep last in-d>> [ value-info ] { } map-as
        ] without-dependencies
    ] [ f ] if* ;

:: splicing-class-infos ( #call input-classes -- infos/f )
    #call word>> name>> input-classes "--- Propagating nodes for infos: %u inputs: %u " format-compiler-message
    #call input-classes propagate-body-for-infos
    deliteralize-infos dup :> res
    [
        #call input-classes res record-inline-propagation
    ] [ f ] if* ;


: trace-non-trivial-infos ( infos -- )
    dup trivial-infos? not [ "--- Using inline-propagated infos %u" sprintf compiler-message ] [ drop ] if ;

:: cached-inline-propagation-infos ( #call word -- classes/f )
    #call inline-signature :> sig
    word inline-info-cache get [ drop H{ } clone ] cache :> info-cache
    sig info-cache at*
    [ "--- inline info cache hit" compiler-message ]
    [
        word sig 2array signature-trace get member?
        [   drop signature-trace get word sig 2array "--- Inline Propagation recursion: %u %u" format-compiler-message
            +inline-recursion+ ]
        [ drop signature-trace [ word sig 2array suffix ] change
          #call sig splicing-class-infos
          dup sig info-cache set-at ] if
    ] if
    dup [ #call word>> sig pick "--- inline infos: %u %u %u" format-compiler-message ] when
    ;

! NOTE: We don't propagate through generic dispatches.  An optimization could be
! to determine whether the input is a proper subset of the generic's method
! definers, and compile in the actual dispatch.
: inline-propagation-infos ( #call word -- classes/f )
    2dup { [ nip primitive? ]
           [ nip generic? ]
           [ nip never-inline-word? ]
           [ nip custom-inlining? ]
           [ drop out-d>> empty? ] } 2||
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
