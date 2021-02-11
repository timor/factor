USING: accessors arrays assocs classes classes.algebra combinators
combinators.short-circuit combinators.short-circuit.smart effects kernel math
sequences sequences.zipped sets words ;

IN: generic.multi


: method-types ( method -- seq ) "method-effect" word-prop effect-in-types reverse ;

: tuple-echelon ( class -- n ) "layout" word-prop third ;

: nth-type ( n method -- seq ) method-types nth ;

: echelon-method? ( class index method -- ? ) nth-type [ tuple-echelon ] same? ;

: method-applicable? ( class index method -- ? ) nth-type class<= ;

: applicable-methods ( class index methods -- seq ) [ method-applicable? ] 2with filter ;

: tuple-dispatch? ( method -- ? ) method-types [ tuple class<= ] all? ;

: echelon-methods ( class index methods -- seq )
    [ { [ echelon-method? ] [ method-applicable? ] } && ] 2with filter ;

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

: haha? ( methods index -- res )
    {
        [ drop length 1 > ]
        [ [ first method-types length ] dip > ]
    } && ;
    ! { [ drop empty? not ] [ [ methlengh ] ] }
    ! over empty?
    ! [ 2drop f ]
    ! [ swap first method-types length < ] if ;

: cleanup-echelon ( assoc -- assoc )


:: haha ( methods index  -- res )
       methods [ method-types index swap nth ] map members
       [| class |
        ! class tuple-echelon :> echelon
        class index methods [ echelon-methods ] [ applicable-methods ] 3bi over diff
        :> ( this-echelon rest-methods )
        this-echelon rest-methods union index 1 + haha?
        [ class this-echelon rest-methods union index 1 + haha 2array ]
        [ class this-echelon rest-methods 3array ] if
       ] map ;

! : foo ( assoc -- res )
!     H{ } clone swap
!     [| method classes |
!      classes assign-dispatch-class :> ( echelon classes' )

!     ] assoc-each ;

:: distribute-echelon ( assoc -- assoc )
    H{ } clone :> res
    assoc [| classes method |
           classes unclip :> ( rest class )
           class tuple-echelon :> echelon
           echelon res [ drop H{ } clone ] cache
           [ rest method 2array class ] dip push-at
     ] assoc-each res ;


:: echelon-tree ( methods -- tree )
    H{ } clone :> res
    methods [
             method-types
             [| class index |
              class tuple-echelon :> echelon
              index res [ drop H{ } clone ] cache
              [ class echelon ] dip push-at
             ] each-index
    ] each res ;
