USING: accessors arrays assocs classes.algebra combinators
combinators.short-circuit combinators.short-circuit.smart effects generic
generic.single generic.single.private generic.standard kernel layouts math
namespaces see sequences sequences.zipped sets vectors words ;

IN: generic.multi

PREDICATE: multi-method < method "method-effect" word-prop ;

GENERIC: method-types ( method -- seq )
M: method method-types "method-class" word-prop 1array ;
M: multi-method method-types
    "method-effect" word-prop effect-in-types reverse ;

: tuple-echelon ( class -- n ) "layout" word-prop third ;

: nth-type ( n method -- seq ) method-types nth ;

: echelon-method? ( class index method -- ? ) nth-type [ tuple-echelon ] same? ;

: method-applicable? ( class index method -- ? ) nth-type class<= ;

: applicable-methods ( class index methods -- seq ) [ method-applicable? ] 2with filter ;

: tuple-dispatch? ( method -- ? ) method-types [ tuple class<= ] all? ;

: echelon-methods ( class index methods -- seq )
    [ { [ echelon-method? ] [ method-applicable? ] } && ] 2with filter ;

: direct-methods ( class index methods -- seq ) [ nth-type class= ] 2with filter ;

! Covariant dispatch tuple
: method< ( method1 method2 -- ? )
    [ method-types ] bi@
    { [ [ class<= ] 2all? ]
      [ <zipped> [ first2 class< ] any? ] } 2&& ;

! ! Associate dispatch classes to methods
! : methods-classes ( methods -- assoc )
!     [ dup method-types ] map>alist ;

: assign-dispatch-class ( classes -- echelon classes' )
    unclip tuple-echelon swap ;

: dispatch-methods ( index methods -- assoc )
    [ [ method-types nth ] keep ] with map>alist ;
    ! flatten-methods ;

: make-dispatch-tree? ( methods index -- res )
    {
        [ drop length 1 > ]
        [ [ first method-types length ] dip > ]
    } && ;
    ! { [ drop empty? not ] [ [ methlengh ] ] }
    ! over empty?
    ! [ 2drop f ]
    ! [ swap first method-types length < ] if ;

:: make-dispatch-tree ( methods index  -- res )
    methods [ method-types index swap nth ] map members
    sort-classes [ flatten-class ] gather
    [| class |
     ! class tuple-echelon :> echelon
     class index methods [ direct-methods ] [ applicable-methods ] 3bi over diff
     :> ( this-echelon rest-methods )
     this-echelon rest-methods union index 1 + make-dispatch-tree?
     [ class this-echelon rest-methods union index 1 + make-dispatch-tree 2array ]
     ! Combine into a single list for now
     ! [ class this-echelon rest-methods 3array ] if
     [ class this-echelon rest-methods union 2array ] if
    ] map ;

: rebalance-inheritance ( class assoc -- assoc )
    clone >vector
    over [ nip class<= ] curry assoc-partition
    swapd [ set-at ] keep
    ! [ keys sort-classes ] [ >alist ] bi extract-keys
    ;

: generic-dispatch-tree ( generic -- tree )
    methods 0 make-dispatch-tree ;

! * Building the engines

TUPLE: tuple-dispatcher assoc n ;
C: <tuple-dispatcher> tuple-dispatcher
TUPLE: tag-dispatcher < tuple-dispatcher ;
C: <tag-dispatcher> tag-dispatcher
TUPLE: external-dispatcher < tuple-dispatcher ;
C: <external-dispatcher> external-dispatcher

: new-dispatcher ( assoc n class -- obj )
    new swap >>n swap >>assoc ;

! cache engines on dispatch index and remaining possibilities
SYMBOL: handled-dispatch

: flat-dispatch? ( subtree -- ? )
    [ sequence? not ] all? ;

ERROR: no-dispatch-error class tree n ;

! each index gets their own cache
: new-cache ( cache class tree n -- cache class tree n )
    [ V{ } clone suffix ] 3dip ;

: diff-cached ( cache class tree n -- cache class tree n )
    ! over hashtable?
    ! [
        [ pick last diff ] dip
    ! ] unless
    ;

: push-cache ( cache class obj tree -- cache class obj )
    dup flat-dispatch? [ reach last push-all ] [ drop ] if ;

DEFER: build-dispatch-assoc
: build-dispatch ( cache tree n type -- dispatcher )
    [ [ build-dispatch-assoc ] keep ] dip new-dispatcher ;

: build-tag-dispatcher ( cache tree n -- dispatcher )
    [ tuple swap rebalance-inheritance ] dip
    tag-dispatcher build-dispatch ;

: build-tuple-dispatcher ( cache tree n -- dispatcher )
    tuple-dispatcher build-dispatch ;


! TODO: handle predicates
: build-dispatch-assoc ( cache tree n -- assoc )
    [                      ! cache [ class subtree n ]
        diff-cached
        [ {
                { [ over assoc-empty? ] [ 2drop f ] }
                { [ pick tuple = ] [ [ over ] 2dip build-tuple-dispatcher ] }
                { [ over flat-dispatch? not ]
                  [ 1 + [ over V{ } clone suffix ] 2dip build-tag-dispatcher ] }
                { [ over length 1 = ] [ drop first ] }
                { [ over length 1 > ] [ no-dispatch-error ] }
            } cond ] keepd ! cache [ class dispatcher subtree ]
        push-cache
    ] curry assoc-map nip ;

: make-dispatch ( tree -- dispatcher )
    V{ } clone 1array swap 0 build-tag-dispatcher ;

! * Compiling the dispatchers
SYMBOL: default-method
SYMBOL: engines
engines [ H{  } clone ] initialize
GENERIC: compile-dispatcher* ( dispatcher -- obj )
DEFER: flatten-dispatch
DEFER: compile-dispatcher
GENERIC: flatten-dispatch* ( dispatcher -- obj )
M: object flatten-dispatch* ;
M: tuple-dispatcher flatten-dispatch*
    [ flatten-dispatch ] change-assoc ;
M: tag-dispatcher flatten-dispatch*
    compile-dispatcher ;

: flatten-dispatch ( assoc -- assoc )
    [ flatten-dispatch*
    ] assoc-map ;

: compile-dispatcher ( dispatcher -- obj )
    [ flatten-dispatch ] change-assoc
    compile-dispatcher* ;

: multi-mega-cache-quot ( methods n -- quot )
    make-empty-cache \ mega-cache-lookup [ ] 4sequence ;

: new-dispatcher-word ( dispatcher quotation -- word )
    "dispatch"  <uninterned-word>
    engines get [ set-at ] keepd
    swap "dispatcher" [ set-word-prop ] keepdd ;

! ** Tag Dispatcher
! Main type of dispatcher, compiles down to a mega-cache-lookup quotation
M: tag-dispatcher compile-dispatcher*
    dup
    [
        assoc>> [ [ tag-number ] dip ] assoc-map
        num-types get default-method get <array> <enumerated> swap assoc-union! seq>>
    ] [ n>> ] bi
    multi-mega-cache-quot new-dispatcher-word ;

! ** Tuple Dispatcher
! Compiles down to a subtree inside the tag dispatcher

M: tuple-dispatcher compile-dispatcher*
    assoc>> echelon-sort ;

! * Interface
: make-multi-dispatch ( generic -- word engines )
    H{ } clone engines [
        generic-dispatch-tree
        make-dispatch
        compile-dispatcher engines get
    ] with-variable ;
