USING: accessors classes.algebra classes.algebra.private kernel sequences types
types.parametric.literal ;

IN: types.encoding

! * Set-theoretic encodings

! ** Row/Record types
! Emulating row-types using intersection and union
! Quite ineffective, don't use for too many entries...
! PREDICATE: index-tag < object \ index-tag eq? ;
! SINGLETON: index-tag
! PREDICATE: label-tag < object \ label-tag eq? ;
! SINGLETON: label-tag

SINGLETON: car-tag
SINGLETON: cdr-tag
ATOM: nil-tag
! ATOM: index-tag
SINGLETON: index-tag

! : <cons> ( car cdr -- type )
    ! [ car-tag class-and ] [ cdr-tag class-and ] bi* class-or ;

: <tag> ( -- type )
    \ <tag> counter <eql> ;

: tons ( car cdr -- type )
    <tag> [ class-and ] curry bi@ dupd class-or class-and ;

: <label> ( label-tag -- type )
    ! <eql> label-tag class-not class-and ;
    ! <eql> class-not ;
    ! <literal-type> class-not ;
    <eql> ;

: <cons> ( car cdr -- type )
    [ "car" <label> class-and ] [ "cdr" <label> class-and ] bi* class-or ;
    ! [ "car" <label> class-and dup class-not ] dip class-and class-or ;
    ! [ dup class-not ] dip class-and class-or ;
: <index> ( number -- type )
    <literal-type> index-tag class-xor ;
    ! <literal-type> index-tag class-not class-and ;
    ! <eql> ;
    ! <literal-type> index-tag class-and ;

ATOM: length-tag
ATOM: type-list

: <type-list> ( type-seq -- type )
    ! [ <index> class-and ] map-index <anonymous-union> ;
    [ length <literal-type> length-tag class-and ]
    [ [ <index> class-and ] map-index <anonymous-union> ] bi class-or
    type-list class-or
    ;


: access-member ( type/union index-type -- type/union )
    swap
    dup null = [ 2drop object ]
    ! Default behavior is undefined, should change to
    ! object instead for row-types? Doing that for now...
    [ 2dup = [ 2drop object ]
    [ dup anonymous-intersection?
      [ participants>> remove <anonymous-intersection> ]
      [ members>> [ access-member ] with map <anonymous-union> ] if ] if ] if ;

: type-nth ( n type-seq -- type )
    [ <index> ] dip over class-and
    access-member ;
