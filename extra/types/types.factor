USING: accessors arrays classes classes.algebra classes.algebra.private
classes.parser classes.predicate classes.private combinators kernel math
sequences sets types.parametric variants ;

IN: types

MIXIN: type

INSTANCE: classoid type

! This is used to convert literal values into corresponding type-values
GENERIC: type-of ( thing -- base-type )

GENERIC: type-or ( type type -- type )

! ! This would be used
! GENERIC: type-and ( type1 type2 -- type )
! M: classoid type-and class-and ;

: define-atom-predicate ( class -- )
    object over [ = ] curry define-predicate-class ;

SYNTAX: ATOM: scan-new-class define-atom-predicate ;


! * Canonicalization
GENERIC: dnf-and* ( classoid classoid -- classoid )
GENERIC: dnf-or* ( classoid classoid -- classoid )
: rank ( classoid classoid -- classoid classoid )
    [ normalize-class ] bi@
    2dup [ rank-class ] bi@ > [ swap ] when ;

! ** Intersection

! ranks 1-2
: <2and> ( class1 class2 -- classoid )
    {
        { [ 2dup classes-intersect? not ]
          [ 2drop null ] }
        { [ 2dup class<= ] [ drop ] }
        { [ 2dup swap class<= ] [ nip ] }
        [ 2array <anonymous-intersection> ]
    } cond ;

: dnf-and ( classoid classoid -- classoid )
    2dup = [ drop ]
    [ rank dnf-and* ] if ;

M: class dnf-and*
    <2and> ;
! rank 2
M: anonymous-predicate dnf-and*
    <2and> ;
! rank 3
M: anonymous-complement dnf-and*
    {
        { [ over anonymous-complement? ] [ [ class>> ] bi@ dnf-or* ] }
        { [ 2dup class>> = ] [ 2drop null ] }
        [ <2and> ]
    } cond ;
! rank 4+5
M: anonymous-intersection dnf-and*
    { { [ over rank-class 3 <
        ] [ participants>> 2dup
            [ classes-intersect? ] with all?
            [
                2dup [ class<= ] with all?
                [ drop ]
                [ swap prefix <anonymous-intersection> ] if
            ]
            [ 2drop null ] if
          ] }
      { [ over anonymous-complement? ]
        [ participants>> 2dup [ class>> ] dip
          member? [ 2drop null ]
          [ swap prefix <anonymous-intersection> ] if ] }
      { [ over anonymous-intersection? ]
        [ [ participants>> ] dip [ dnf-and* ] curry map [ participants>> ]
          gather <anonymous-intersection> ] }
    } cond ;
! rank 6+7
M: anonymous-union dnf-and*
    { { [ over rank-class 5 < ] [
            members>>
            [ dnf-and* ] with map <anonymous-union>
            ! 2dup [ class<= ] with all?
            ! [ nip <anonymous-union> ]
            ! [ swap prefix <anonymous-union> ]
            ! if
        ] }
      ! { [ over anonymous-complement? ]
      !   [ members>> 2dup [ class>> ] dip
      !     member? [ 2drop object ]
      !     [ swap prefix <anonymous-union> ] if ] }
      ! { [ over anonymous-intersection? ]
      !   [ members>> [ dnf-and* ] with map <anonymous-union> ] }
      { [ over anonymous-union? ]
        [ [ members>> ] dip [ dnf-and* ] curry gather <anonymous-union> ] }
    } cond ;
! >8 (mixin)
M: classoid dnf-and*
    <2and> ;

! ** Union

: <2or> ( class1 class2 -- classoid )
    {
        ! { [ 2dup classes-intersect? not ]
        !   [ 2drop null ] }
        { [ 2dup class<= ] [ nip ] }
        { [ 2dup swap class<= ] [ drop ] }
        [ 2array <anonymous-union> ]
    } cond ;

: dnf-or ( classoid classoid -- classoid )
    2dup = [ drop ]
    [ rank dnf-or* ] if ;

! ranks 1-2
M: class dnf-or*
    <2or> ;
! rank 2
M: anonymous-predicate dnf-or*
    <2or> ;
! rank 3
M: anonymous-complement dnf-or*
    {
        { [ over anonymous-complement? ] [ [ class>> ] bi@ dnf-and* ] }
        { [ 2dup class>> = ] [ 2drop null ] }
        [ <2and> ]
    } cond ;
! rank 4+5
M: anonymous-intersection dnf-or*
    { { [ over rank-class 5 < ]
        [ <2or> ] }
    } cond ;
! rank 6+7
M: anonymous-union dnf-or*
    { { [ over rank-class 3 < ] [
            members>>
            2dup [ class<= ] with all?
            [ nip <anonymous-union> ]
            [ swap prefix <anonymous-union> ]
            if ] }
      { [ over anonymous-complement? ]
        [ members>> 2dup [ class>> ] dip
          member? [ 2drop object ]
          [ swap prefix <anonymous-union> ] if ] }
      { [ over anonymous-intersection? ]
        [ members>> [ dnf-and* ] with map <anonymous-union> ] }
      { [ over anonymous-union? ]
        [ [ members>> ] dip [ dnf-and* ] curry gather <anonymous-union> ] }
    } cond ;
! >8 (mixin)
M: classoid dnf-or*
    <2or> ;

! List of intersections
! TUPLE: dnf positives negatives ;
! UNION: atomic class anonymous-predicate ;
! VARIANT: dnf-pair
!     +0+
!     +1+
!     canonical: { { positive sequence read-only
!                  } { negative sequence read-only } }
!     ;

! : <1pos> ( atom -- dnf-pair )
!     1array { } <canonical> ;
! : <1neg> ( atom -- dnf-pair )
!     1array { } swap <canonical> ;

! : dnf-intersect-positive ( dnf-pair atomic -- dnf-pair )
!     swap
!     {
!         { +1+ [ <1pos> ] }
!         { +0+ [ drop +0+ ] }
!         { canonical [| atom pos neg |
!                      { { [ atom neg in? ] [ +0+ ] }
!                        { [ atom pos [ classes-intersect? ] with any? not ] [ +0+ ] }
!                        [ pos atom suffix sort-classes neg <canonical> ]
!                      } cond
!                     ] }
!     }
!     match ;

! : dnf-intersect-negative ( dnf-pair atomic -- dnf-pair )
!     swap
!     {
!         { +1+ [ <1neg> ] }
!         { +0+ [ drop +0+ ] }
!         { canonical [| atom pos neg |
!                      { { [ atom pos in? ] [ +0+ ] }
!                        ! { [ atom pos [ classes-intersect? ] with any? not ] [ +0+ ] }
!                        [ pos neg atom suffix sort-classes <canonical> ]
!                      } cond
!                     ] }
!     }
!     match ;

! : dnf-union-positive ( dnf atomic -- dnf )


! : dnf-union-positive ( dnf-pair atomic -- dnf-pair )
!     swap
!     {
!         { +1+ [ drop +1+ ] }
!         { +0+ [ <1pos> ] }
!         ! TODO: is it allowed to do the subtype check here?
!         { canonical [| atom pos neg |
!                      { { [ atom neg in? ] [ +1+ ] }
!                        { [ atom pos [ class<= ] with all? ]
!                          [ pos neg <canonical> ] }
!                        [ pos neg atom suffix sort-classes <canonical> ]
!                      } cond
!                     ] }
!     }
!     match ;

! : dnf-union-negative ( dnf-pair atomic -- dnf-pair )
!     swap
!     {
!         { +1+ [ drop +1+ ] }
!         { +0+ [ <1neg> ] }
!         { canonical [| atom pos neg |
!                      { { [ atom pos in? ] [ +1+ ] }
!                        ! { [ atom pos [ class<= ] with all? ]
!                        !   [ pos neg <canonical> ] }
!                        [ pos neg atom suffix sort-classes <canonical> ]
!                      } cond
!                     ] }
!     }
!     match ;

! C: <class-dnf> class-dnf
! : class-dnf-union ( dnf-pair dnf-pair -- dnf-pair )
!     [ [ positive>> ] [ negative>> ] bi ] bi@ <class-dnf> ;
! : complementary? ( atom atom -- ? )

! : class-dnf-intersection ( dnf-pair dnf-pair -- dnf-pair )

! : class-dnf-complement ( dnf-pair -- dnf-pair )

! GENERIC: >dnf ( type -- dnf-pair )
! M: atomic >dnf 1array f <class-dnf> ;
! M: anonymous-complement >dnf
!     dup class>> atomic?
!     [ 1array f swap <class-dnf> ]
! GENERIC: rebuild-dnf ( class -- positives negatives )
! M: atomic rebuild-dnf 1array f ;
! M: anonymous-complement rebuild-dnf
! M:
! : trivial-union? ( members -- ? )
!     [ anonymous-complement? ] partition
!     [ [ class>> ] dip = ] cartesian-find and ;

! ! Bring into dnf-pair form and perform simplifications (possibly quite expensive)
! GENERIC: class-dnf ( classoid -- classoid )
! M: anonymous-union class-dnf
!     members>> [ class-dnf ] map
!     [ anonymous-union? ] partition swap
!     [ members>> ] gather union
!     dup trivial-union? [ drop intersection{ } ]
!     [ <anonymous-union> ] if ;

! : trivial-empty-intersection? ( participants -- ? )
!     [ anonymous-complement? ] partition
!     [ [ class>> ] dip = ] cartesian-find and ;

! ! Any negatives that don't intersect with anything can be dropped
! : drop-negatives ( participants -- participants )
!     [ anonymous-complement? ] partition swap
!     [ class>> [ classes-intersect? ] with any? ] with filter ;

! : trivial-full-intersection? ( participants -- ? )
!     [ null = ] any? ;

! : simplify-de-morgan ( participants -- class/f )
!     dup [ anonymous-complement? ] all?
!     [ [ class>> ] map <anonymous-union> ] [ drop f ] if ;

! : distribute-unions ( participants -- class/f )
!     dup [ anonymous-union? ] any?
!     [ [ dup anonymous-union? [ members>> ] [ 1array ] if ]
!       [ [ class-and ] cartesian-product concat <anonymous-union> ]
!       map-reduce
!     ] [ drop f ] if ;

! M: anonymous-intersection class-dnf
!     participants>> [ class-dnf ] map
!     [ anonymous-intersection? ] partition swap
!     [ participants>> ] gather union
!     dup { [ simplify-de-morgan ] [ distribute-unions ] } 1|| [ nip class-dnf ]
!     [
!         { [ dup trivial-empty-intersection? ] [ drop null ] }
!         apply-de-morgan
!       dup anonymous-intersection? [
!           dup trivial-empty-intersection?
!           [ drop null ] [ <anonymous-intersection> ] if
!       ] [ class-dnf ] if ] if* ;


! ! * Disjoint Union
! : class-xor ( class1 class2 -- class )
!     [ class-not class-and ] [ [ class-not ] dip class-and ] 2bi class-or ;
