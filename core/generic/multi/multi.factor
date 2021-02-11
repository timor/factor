USING: accessors arrays assocs classes classes.algebra combinators
combinators.short-circuit combinators.short-circuit.smart effects generic kernel
math see sequences sequences.zipped sets words ;

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

! Associate dispatch classes to methods
: methods-classes ( methods -- assoc )
    [ dup method-types ] map>alist ;

: assign-dispatch-class ( classes -- echelon classes' )
    unclip tuple-echelon swap ;

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
    sort-classes
    [| class |
     ! class tuple-echelon :> echelon
     class index methods [ direct-methods ] [ applicable-methods ] 3bi over diff
     :> ( this-echelon rest-methods )
     this-echelon rest-methods union index 1 + make-dispatch-tree?
     [ class this-echelon rest-methods union index 1 + make-dispatch-tree 2array ]
     [ class this-echelon rest-methods 3array ] if
    ] map ;

: generic-dispatch-tree ( generic -- tree )
    methods 0 make-dispatch-tree ;
