USING: accessors arrays assocs byte-arrays combinators.short-circuit
compiler.messages compiler.tree compiler.tree.builder.private
compiler.tree.normalization compiler.tree.propagation.info
compiler.tree.propagation.inlining compiler.tree.propagation.nodes
compiler.tree.recursive compiler.utilities continuations formatting generic
kernel locals math namespaces sequences stack-checker.dependencies
stack-checker.errors strings words ;

IN: compiler.tree.propagation.inline-propagation


! An assoc storing cached inlined-infos for different value-info inputs for each word

: word-inline-infos-cache ( word -- assoc )
    dup "inline-propagation-infos" word-prop
    [ nip ] [ H{ } clone [ "inline-propagation-infos" set-word-prop ] keep ] if* ;

UNION: primitive-sequence string byte-array array ;

ERROR: null-value-info ;
: assert-non-null-info ( value-info -- )
    null-info = [ null-value-info ] when ;

: convex-input-info ( value-info -- value-info )
    class>> <class-info> ;
    ! dup assert-non-null-info
    ! dup literal>>
    ! { { [ dup primitive-sequence? ] [ drop [ slots>> first ] [ class>> ] bi <sequence-info> ] }
    !   { [ dup tuple? ] [ drop [ slots>> ] [ class>> ] bi <tuple-info> ] }
    !   [ drop [ class>> ] [ interval>> ] bi <class/interval-info> ] } cond
    ! ! dup { [ interval>> special-interval? not ]
    ! !       [ literal>> identity-tuple? ]
    ! !       [ literal>> { [ word? ] [ name>> "( gensym )" = ] } 1&& ]
    ! !       [ literal>> quotation? ]
    ! !       [ literal>> { [ primitive-sequence? ] [ empty? not ] } 1&& ]
    ! ! } 1||
    ! ! [ class>> <class-info> ] when
    ! dup slots>> [
    !     ! [ clone ] dip
    !     [ dup [ convex-input-info ] when ] map
    !     >>slots
    ! ] when*
    ! ! dup assert-non-null-info
    ! ;

    ! dup interval>> special-interval?
    ! [ class>> <class-info> ] unless
    ! dup slots>> [
    !     [ clone ] dip
    !     [ dup [ convex-input-info ] when ] map
    !     >>slots
    ! ] when* ;
    ! ! dup literal?>> [ class>> <class-info> ] when ;

: inline-signature ( #call -- obj )
    in-d>> [ value-info class>> ] map ;

: deliteralize-infos ( #call infos -- infos )
    swap word>> foldable? [ [ class>> <class-info> ] map ] unless ;
    ! [ [ f >>literal? f >>literal? ] map ] unless ;

: trivial-infos? ( infos -- ? )
    [ { [ object-info = ] [ class>> union{ t POSTPONE: f } = ] } 1|| ] all? ;

! : record-inline-propagation ( #call infos -- )
!     trivial-infos? [ drop ] [ word>> +definition+ depends-on ] if ;
: record-inline-propagation ( word input-classes infos -- )
    [ class>> ] map
    [ [ add-depends-on-class ] each ] bi@
    +definition+ depends-on ;

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

: cached-inline-propagation-body ( #call -- nodes/f )
    [ word>> ] keep over "inline-body" word-prop
    [ 2nip ]
    [ inline-propagation-body [ "inline-body" set-word-prop ] keep ] if* ;

: propagate-body-for-infos ( #call input-classes -- infos/f )
    [ <class-info> ] map
    swap ! cached-
    inline-propagation-body
    [ [
                value-infos [ H{ } clone suffix ] change
                [ first dup #copy? [ in-d>> ] [ drop f ] if [ set-value-info ] 2each ] keep
                [ (propagate) ] keep last in-d>> [ value-info ] map
            ] with-scope
    ] [ drop f ] if*
    ;

:: splicing-class-infos ( #call input-classes -- infos/f )
    #call word>> name>> "--- Propagating nodes for infos: " prepend compiler-message
    #call input-classes propagate-body-for-infos dup :> res
    [
        #call swap deliteralize-infos
        #call word>> input-classes res record-inline-propagation
    ] [ f ] if* ;

: trace-non-trivial-infos ( infos -- )
    dup trivial-infos? not [ "--- Using inline-propagated infos %u" sprintf compiler-message ] [ drop ] if ;

:: cached-inline-propagation-infos ( #call word -- infos/f )
    #call inline-signature :> sig
    word word-inline-infos-cache :> info-cache
    word sig 2array signature-trace get member?
    [ +inline-recursion+ ]
    [
        sig info-cache at
        [ signature-trace [ word sig 2array suffix ] change
        #call sig splicing-class-infos ] unless*
        dup sig info-cache set-at
    ] if
    ;

! NOTE: We don't propagate through generic dispatches.  An optimization could be
! to determine whether the input is a proper subset of the generic's method
! definers, and compile in the actual dispatch.
: inline-propagation-infos ( #call word -- infos/f )
    2dup { [ nip primitive? ]
           [ nip generic? ]
           [ nip never-inline-word? ]
           [ nip custom-inlining? ]
           [ drop out-d>> empty? ] } 2||
    [ 2drop f ]
    [ cached-inline-propagation-infos
      dup +inline-recursion+? [ drop f ] when
    ] if
    dup trace-non-trivial-infos
    ;
