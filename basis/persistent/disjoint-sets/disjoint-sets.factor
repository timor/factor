USING: accessors assocs combinators disjoint-sets kernel math persistent.assocs
persistent.hashtables.identity persistent.sequences persistent.vectors sequences
;

IN: persistent.disjoint-sets


! Efficient Disjoint Set implementation based on
! Conchon, Sylvain, and Jean-Christophe Filliâtre. "A persistent union-find data structure." Proceedings of the 2007 workshop on Workshop on ML. 2007.


! Note that we use persistent.vectors as underlying storage, as well as
! persistent.hashtable for element->index mapping. This should save some cycles
! when doing the path-following.


! TODO: maybe implement the existing disjoint-set interface on a reference type

! TODO: maybe implement immediate parent check

TUPLE: persistent-union-find
    { imap id-persistent-hash read-only }
    { pami persistent-vector read-only }
    { ranks persistent-vector read-only }
    { parents persistent-vector } ! modified in-place for path compression
;

C: <persistent-union-find> persistent-union-find

ERROR: not-a-member element disjoint-set ;

<PRIVATE
:: new-index ( atom puf -- map pam i )
    puf imap>> :> imap
    puf pami>> :> pami
    pami length :> i
    i atom imap new-at
    atom pami ppush
    i ; inline

: item-at ( key imap -- value )
    [ ?at ] keep swap
    [ drop ]
    [ not-a-member ] if ; inline

: item>index ( a puf -- i puf )
    [ imap>> item-at ] keep ; inline

: 2item>index ( a b puf -- i j puf )
    [ imap>> [ item-at ] curry bi@ ] keep ; inline

: index>item ( i puf -- a puf )
    [ pami>> nth ] keep ; inline

: find-aux ( i parents -- r parents' )
    2dup nth pick over =
    [ drop ]
    [| i p1 fi |
     fi p1 find-aux :> ( r p2 )
     r dup i p2 new-nth
    ] if ;
! TODO: make inline recursive?

: find-rep ( i puf! -- r )
    [ find-aux ] change-parents drop ;

PRIVATE>

: added-atom ( atom puf: persistent-union-find -- puf )
    [ new-index ] keep
    [ parents>> ppush ]
    [ ranks>> 0 swap ppush ] bi
    swap <persistent-union-find>
    ;

:: equated ( a b puf -- puf )
    a b puf 2item>index :> ( x y puf )
    x y [ puf find-rep ] bi@ :> ( cx cy )
    cx cy = [ puf ]
    [
        puf { [ imap>> ] [ pami>> ] [ parents>> ] [ ranks>> ] } cleave :> ( imap pami parents ranks )
        cx ranks nth :> rx
        cy ranks nth :> ry
        imap pami
        rx ry = [
            rx 1 + cx ranks new-nth
            cx cy
        ] [
            ranks
            rx ry > [ cx cy ] [ cy cx ] if
        ] if
        parents new-nth
        <persistent-union-find>
    ] if ;

M: persistent-union-find clone ;

! non-persistent interface can be implemented

M: persistent-union-find representative
    item>index
    [ find-rep ] keep pami>> nth ;

M: persistent-union-find disjoint-set-member?
    imap>> key? ;
M: persistent-union-find disjoint-set-members
    pami>> ;
M: persistent-union-find equiv?
    2item>index
    [ find-rep ] curry bi@ = ;
