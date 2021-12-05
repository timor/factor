USING: accessors arrays classes classes.algebra classes.algebra.private
combinators effects formatting kernel math math.intervals math.parser sequences
types types.parametric ;

IN: types.parametric.intervals

! * Typing numeric values using intervals

TUPLE: interval-type < anonymous-predicate
    interval ;
: <interval-type> ( superclass interval -- class )
    [ interval>> interval-contains? ] swap interval-type boa ;

M: interval-type parameter-classes-intersect?
    ! Only have to consider other interval types here, as intersection with
    ! superclasses has already been checked
    ! NOTE: That is incorrect, we must assume that unrelated predicates with the
    ! same superclass intersect unless defined otherwise.
    over interval-type?
    [ [ interval>> ] bi@ intervals-intersect? ]
    [ 2drop t ] if ;

M: interval-type custom-class-complement? drop t ;
! Several cases:
! 1. interval is unbounded in both endpoints:  empty interval
! 2. interval is empty: full-interval
! 3. interval is lower-bounded: return non-containing upper interval
! 4. interval is upper-bounded: return non-containing lower interval
! 5. interval is bounded in both directions: return disjoint union of both of the above
! : upper-interval-complement ( lower upper -- interval/f )
: interval-complement ( interval -- lower upper )
    interval>points swap
    [ first2 not 2array 1/0. t 2array <interval> ]
    [ first2 not 2array -1/0. t 2array swap <interval> ] bi* ;

: make-complement-interval-type ( superclass lower upper -- type )
    { { [ 2dup [ empty-interval? ] both? ] [ 3drop null ] }
      { [ 2dup [ full-interval? ] either? ] [ 2drop ] }
      { [ 2dup [ empty-interval? ] either? ]
        [ dup empty-interval? [ drop ] [ nip ] if <interval-type> ] }
      [ [ <interval-type> ] bi-curry@ bi class-or ]
    } cond ;

! NOTE: complement operation is currently not reversible!
! A union of even overlapping types will only pass the subclass check in one direction!
! However, this should not pose a problem since this is only used in
! lowest-level intersection checks, and not used for class-not in general...
M: interval-type custom-class-complement
    [ superclass-of ] [ interval>> ] bi
    interval-complement
    make-complement-interval-type ;

GENERIC: endpoint>string ( number -- string )

M: integer endpoint>string
    dup abs 1000 <
    [ number>string ]
    [ [ 0 < "-" "" ? "2^" prepend ] [ abs log2 "%.2f" sprintf append ] bi ] if ;

M: number endpoint>string
    "%.2f" sprintf ;

: math-class>string ( class -- string )
    { { [ dup integer class<= ] [ drop "ℤ" ] }
      { [ dup ratio class<= ] [ drop "ℚ" ] }
      { [ dup real class<= ] [ drop "ℝ" ] }
      { [ dup complex class<= ] [ drop "ℂ" ] }
      [ effect>string ]
    } cond ;

: interval-points>string ( from to -- prefix suffix )
    2dup = [ drop first endpoint>string "=" prepend "" swap ]
    [
        [ first2 [ endpoint>string ] [ "≤" "<" ? ] bi* append ]
        [ first2 [ endpoint>string ] [ "≤" "<" ? ] bi* swap append ] bi*
    ] if ;

M: interval-type effect>string
    [ superclass-of math-class>string ]
    [ interval>> interval>points
      interval-points>string
    ] bi surround ;

! : <ranged> ( lower upper -- class )
!     [a,b] number swap <interval-type> ;
M: number type-of
    [ class-of ] [ [a,a] ] bi <interval-type> ;
