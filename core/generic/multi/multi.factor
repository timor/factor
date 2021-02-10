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

: echelon-methods ( class index methods -- seq ) [ echelon-method? ] 2with filter ;

! Covariant dispatch tuple
: method< ( method1 method2 -- ? )
    [ method-types ] bi@
    { [ [ class<= ] 2all? ]
      [ <zipped> [ first2 class< ] any? ] } 2&& ;

: methods-dispatch-classes ( methods index -- seq )
    [ swap method-types nth ] curry map members ;

:: cut-echelon ( methods index echelon -- assoc )
    methods index methods-dispatch-classes
    [ tuple-echelon echelon = ] filter
    [ dup index methods echelon-methods ] map>alist ;

: max-echelon ( methods index -- n )
    methods-dispatch-classes [ tuple-echelon ] map supremum ;

DEFER: make-tuple-dispatch-tree
: refine-echelon ( methods index -- methods )
    { { [ over empty? ] [ 2drop f ] }
        { [ over length 1 > ] [ make-tuple-dispatch-tree ] }
        [ drop ]
      } cond ;

: make-tuple-dispatch-tree? ( methods index -- ? )
    { [ drop empty? not ]
      [ [ first method-types length ] dip > ]
    } && ;


: make-tuple-dispatch-tree ( methods index -- seq )
    2dup make-tuple-dispatch-tree? not
    [ drop ]
    [ 2dup max-echelon 1 +
      [ [ cut-echelon ] keepd 1 +
        [ refine-echelon ] curry assoc-map
      ] 2with { } map-integers ] if ;

! : method-tuple-dispatch-tree ( methods index -- seq )
!     over method-types [ swap nth ] curry map



