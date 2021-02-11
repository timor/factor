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

! NOTE: we don't check for equality here.  As long as there are no duplicates,
! that should be valid.
: method-redundant? ( method methods -- ? )
    [ swap method< ] with any? ;

: dispatchable-methods ( class index methods -- seq )
    [ echelon-methods dup . ]
    [ applicable-methods dup . ] 3bi
    over [ method-redundant? ] curry reject union ;

: methods-dispatch-classes ( methods index -- seq )
    [ swap method-types nth ] curry map members ;

! Methods that can still be dispatched to:
! 1. Methods specialized at current index on the same echelon
! 1. Methods specialized at current index on a lower echelon, but which are not ...
:: cut-echelon ( methods index echelon -- assoc )
    methods index methods-dispatch-classes
    [ tuple-echelon echelon = ] filter
    [ dup index methods applicable-methods ] map>alist ;

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



