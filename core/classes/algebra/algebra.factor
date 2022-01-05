! Copyright (C) 2004, 2010 Slava Pestov.
! See http://factorcode.org/license.txt for BSD license.
USING: accessors arrays assocs classes classes.private
combinators kernel make math math.order math.parser namespaces sequences
sets sorting vectors words ;
IN: classes.algebra

DEFER: sort-classes

<PRIVATE

TUPLE: anonymous-union { members read-only } ;

INSTANCE: anonymous-union classoid

: <anonymous-union> ( members -- classoid )
    [ classoid check-instance ] map [ null eq? ] reject
    members dup length 1 =
    [ first ] [ sort-classes f like anonymous-union boa ] if ;

M: anonymous-union rank-class drop 6 ;

TUPLE: anonymous-intersection { participants read-only } ;

INSTANCE: anonymous-intersection classoid

: <anonymous-intersection> ( participants -- classoid )
    [ classoid check-instance dup anonymous-intersection? [ members>> ] [ 1array ] if ] gather
    dup length 1 =
    [ first ] [ sort-classes f like anonymous-intersection boa ] if ;

M: anonymous-intersection rank-class drop 4 ;

TUPLE: anonymous-complement { class read-only } ;

INSTANCE: anonymous-complement classoid

: <anonymous-complement> ( object -- classoid )
    classoid check-instance anonymous-complement boa ;

M: anonymous-complement rank-class drop 3 ;

M: anonymous-complement instance?
    over [ class>> instance? not ] [ 2drop t ] if ;

M: anonymous-complement class-name
    class>> class-name ;

DEFER: (class<=)

DEFER: (class-not)

GENERIC: (classes-intersect?) ( first second -- ? )

DEFER: (class-and)

DEFER: (class-or)

GENERIC: (flatten-class) ( class -- )

GENERIC: normalize-class ( class -- class' )

M: object normalize-class ;

: symmetric-class-op ( first second cache quot -- result )
    [ 2dup [ rank-class ] bi@ > [ swap ] when ] 2dip 2cache ; inline

PRIVATE>

! Wrapper semantics: singleton class of any value.  The only instance is the
! value.  It's superclass is the class of the value.  It describes the arrow
! type of a word that pushes the object when evaluated.  The rank is set
! slightly above the other atomic classes but below predicate classes because
! their intersection checks only test the superclass level.  Nevertheless, they
! should be ordered before predicate classes in method dispatch, because they
! are more specific in general.
INSTANCE: wrapper classoid
M: wrapper instance?
    wrapped>> = ;
M: wrapper rank-class drop 1+1/2 ;

M: wrapper superclass-of wrapped>> class-of  ; inline
M: wrapper (flatten-class) superclass-of (flatten-class) ;

GENERIC: singleton-suffix ( object -- str )
M: object singleton-suffix
    identity-hashcode number>string ;
M: word singleton-suffix
    name>> ;

M: wrapper class-name
    [ superclass-of class-name "_" append ]
    [ wrapped>> singleton-suffix append ] bi ;

! For implementing word interface
! NOTE: not using vocabulary name here!
M: wrapper name>>
    class-name ;

M: wrapper vocabulary>>
    superclass-of vocabulary>> ;

! Copy-pasted from M\ word <=>
M: wrapper <=>
    [ [ name>> ] [ vocabulary>> ] bi 2array ] compare ;

! Gradual type
SINGLETON: ??
INSTANCE: ?? classoid
M: ?? rank-class drop 9 ;
M: ?? (classes-intersect?) 2drop t ;

: only-classoid? ( obj -- ? )
    dup classoid? [ class? not ] [ drop f ] if ;

: class<= ( first second -- ? )
    class<=-cache get [ (class<=) ] 2cache ;

: class< ( first second -- ? )
    {
        { [ 2dup class<= not ] [ 2drop f ] }
        { [ 2dup swap class<= not ] [ 2drop t ] }
        [ [ rank-class ] bi@ < ]
    } cond ;

: class= ( first second -- ? )
    2dup class<= [ swap class<= ] [ 2drop f ] if ;

: class-not ( class -- complement )
    class-not-cache get [ (class-not) ] cache ;

: classes-intersect? ( first second -- ? )
    [ normalize-class ] bi@
    classes-intersect-cache get [ (classes-intersect?) ] symmetric-class-op ;

M: wrapper (classes-intersect?)
    { { [ over wrapper? ] [ = ] }
      [ superclass-of classes-intersect? ]
    } cond ;

: class-and ( first second -- class )
    class-and-cache get [ (class-and) ] symmetric-class-op ;

: class-or ( first second -- class )
    class-or-cache get [ (class-or) ] symmetric-class-op ;

SYMBOL: +incomparable+

: compare-classes ( first second -- <=> )
    [ swap class<= ] [ class<= ] 2bi
    [ +eq+ +lt+ ] [ +gt+ +incomparable+ ] if ? ;

: evaluate-class-predicate ( class1 class2 -- ? )
    {
        { [ 2dup class<= ] [ t ] }
        { [ 2dup classes-intersect? not ] [ f ] }
        [ +incomparable+ ]
    } cond 2nip ;

<PRIVATE

! Special-case wrappers here to delegate class<= check to algebra
: superclass<= ( first second -- ? )
    swap dup wrapper? [ drop f ] [ superclass-of ] if
    [ swap class<= ] [ drop f ] if* ;

: left-anonymous-union<= ( first second -- ? )
    [ members>> ] dip [ class<= ] curry all? ;

: right-union<= ( first second -- ? )
    class-members [ class<= ] with any? ;

: right-anonymous-union<= ( first second -- ? )
    members>> [ class<= ] with any? ;

: left-anonymous-intersection<= ( first second -- ? )
    [ participants>> ] dip [ class<= ] curry any? ;

PREDICATE: nontrivial-anonymous-intersection < anonymous-intersection
    participants>> empty? not ;

: right-anonymous-intersection<= ( first second -- ? )
    participants>> [ class<= ] with all? ;

: anonymous-complement<= ( first second -- ? )
    [ class>> ] bi@ swap class<= ;

: normalize-complement ( class -- class' )
    class>> normalize-class {
        { [ dup anonymous-union? ] [
            members>>
            [ class-not normalize-class ] map
            <anonymous-intersection>
        ] }
        { [ dup anonymous-intersection? ] [
            participants>>
            [ class-not normalize-class ] map
            <anonymous-union>
        ] }
        [ drop object ]
    } cond ;

: left-anonymous-complement<= ( first second -- ? )
    [ normalize-complement ] dip class<= ;

PREDICATE: nontrivial-anonymous-complement < anonymous-complement
    class>> {
        [ anonymous-union? ]
        [ anonymous-intersection? ]
        [ class-members ]
        [ class-participants ]
    } cleave or or or ;

PREDICATE: empty-union < anonymous-union members>> empty? ;

PREDICATE: empty-intersection < anonymous-intersection participants>> empty? ;
! NOTE: this is only asks for the inverse in the subdomain of the class, since
! superclass ordering has already been checked
GENERIC: custom-class-complement? ( class -- ? )
GENERIC: custom-class-complement ( class -- class )
M: object custom-class-complement? drop f ;


GENERIC: custom-class-order? ( class -- ? )
M: object custom-class-order? drop f ;
GENERIC: custom-class<= ( first second -- ? )



: left-wrapper<= ( wrapper non-wrapper -- ? )
    classes-intersect? ;

: right-wrapper<= ( non-wrapper wrapper -- ? )
    2drop f ;

: (class<=) ( first second -- ? )
    2dup eq? [ 2drop t ] [
        [ normalize-class ] bi@
        2dup [ ??? ] either? [ 2drop f ] [
            2dup superclass<= [ 2drop t ] [
                {
                    { [ 2dup eq? ] [ 2drop t ] }
                    { [ dup empty-intersection? ] [ 2drop t ] }
                    { [ over empty-union? ] [ 2drop t ] }
                    { [ 2dup [ anonymous-complement? ] both? ] [ anonymous-complement<= ] }
                    { [ over anonymous-union? ] [ left-anonymous-union<= ] }
                    { [ over nontrivial-anonymous-intersection? ] [ left-anonymous-intersection<= ] }
                    { [ over nontrivial-anonymous-complement? ] [ left-anonymous-complement<= ] }
                    { [ dup class-members ] [ right-union<= ] }
                    { [ dup anonymous-union? ] [ right-anonymous-union<= ] }
                    { [ dup anonymous-intersection? ] [ right-anonymous-intersection<= ] }
                    { [ dup anonymous-complement? ] [ class>> classes-intersect? not ] }
                    { [ 2dup [ wrapper? ] both? ] [ = ] }
                    { [ over wrapper? ] [ left-wrapper<= ] }
                    { [ dup wrapper? ] [ right-wrapper<= ] }
                    ! { [ dup custom-class-order? ] [ class-not classes-intersect? not ] }
                    { [ dup custom-class-complement? ] [ custom-class-complement classes-intersect? not ] }
                    [ 2drop f ]
                } cond
            ] if
        ] if
    ] if ;

M: anonymous-union (classes-intersect?)
    members>> [ classes-intersect? ] with any? ;

M: anonymous-intersection (classes-intersect?)
    participants>> [ classes-intersect? ] with all? ;

M: anonymous-complement (classes-intersect?)
    class>> class<= not ;

: anonymous-union-and ( first second -- class )
    members>> [ class-and ] with map <anonymous-union> ;

: anonymous-intersection-and ( first second -- class )
    participants>> swap suffix <anonymous-intersection> ;

: (class-and) ( first second -- class )
    2dup compare-classes {
        { +lt+ [ drop ] }
        { +gt+ [ nip ] }
        { +eq+ [ nip ] }
        { +incomparable+ [
            2dup classes-intersect? [
                2dup [ ??? ] either? [ class-or ]
                [
                    [ normalize-class ] bi@ {
                        { [ dup anonymous-union? ] [ anonymous-union-and ] }
                        { [ dup anonymous-intersection? ] [ anonymous-intersection-and ] }
                        { [ over anonymous-union? ] [ swap anonymous-union-and ] }
                        { [ over anonymous-intersection? ] [ swap anonymous-intersection-and ] }
                        [ 2array <anonymous-intersection> ]
                    } cond
                ] if
            ] [ 2drop null ] if
        ] }
    } case ;

: anonymous-union-or ( first second -- class )
    members>> swap suffix <anonymous-union> ;

: classes>anonymous-union ( first second -- class )
    [ normalize-class ] bi@ {
        { [ dup anonymous-union? ] [ anonymous-union-or ] }
        { [ over anonymous-union? ] [ swap anonymous-union-or ] }
        [ 2array <anonymous-union> ]
    } cond ;

: anonymous-complement-or ( first second -- class )
    2dup class>> swap class<= [ 2drop object ] [ classes>anonymous-union ] if ;

: (class-or) ( first second -- class )
    2dup compare-classes {
        { +lt+ [ nip ] }
        { +gt+ [ drop ] }
        { +eq+ [ nip ] }
        { +incomparable+ [
            {
                { [ dup anonymous-complement? ] [ anonymous-complement-or ] }
                { [ over anonymous-complement? ] [ swap anonymous-complement-or ] }
                [ classes>anonymous-union ]
            } cond
        ] }
    } case ;

: (class-not) ( class -- complement )
    {
        { [ dup ??? ] [ ] }
        { [ dup anonymous-complement? ] [ class>> ] }
        { [ dup object eq? ] [ drop null ] }
        { [ dup null eq? ] [ drop object ] }
        [ <anonymous-complement> ]
    } cond ;

M: anonymous-union (flatten-class)
    members>> [ (flatten-class) ] each ;

PRIVATE>

ERROR: topological-sort-failed ;

: largest-class ( seq -- n elt )
    dup [ [ class< ] with none? ] curry find-last
    [ topological-sort-failed ] unless* ;

: sort-classes ( seq -- newseq )
    [ class-name ] sort-with >vector
    [ dup empty? not ]
    [ dup largest-class [ swap remove-nth! ] dip ]
    produce nip ;

: smallest-class ( classes -- class/f )
    [ f ] [
        natural-sort <reversed>
        [ ] [ [ class<= ] most ] map-reduce
    ] if-empty ;

: flatten-class ( class -- seq )
    [ (flatten-class) ] { } make members ;
