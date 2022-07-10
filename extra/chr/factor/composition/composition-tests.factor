USING: accessors arrays assocs chr.factor.composition chr.parser kernel
kernel.private lists sequences slots.private terms tools.test typed ;
IN: chr.factor.composition.tests

: nop ( -- ) ;
GENERIC: mylastcdr ( list -- obj )
M: list mylastcdr

    ! RES3 needed for [ mylastcdr ]
    ! not working with [ [ mylastcdr ] ] (neither RES1,2,3 cause progress)
    ! RES2 needed for [ [ mylastcdr ] (call) ]
    ! cdr>> [ mylastcdr ] (call) ;

    ! HA! This works with RES2!
    ! cdr>> [ nop mylastcdr ] (call) ;

    ! nop cdr>> [ mylastcdr ] (call) ;

    ! cdr>> nop [ mylastcdr ] (call) ;


    cdr>> [ [ mylastcdr ] ] (call) (call) ; ! Doesnt work so well...

    ! RES3 needed for [ mylastcdr ]
    ! RES1 needed for [ [ mylastcdr ] ]
    ! RES3 needed for [ [ mylastcdr ] (call) ]
    ! RES2 needed for [ [ [ mylastcdr ] (call) ] (call) ]
    ! RES1 needed for [ [ [ mylastcdr ] ] (call) (call) ]
    ! cdr>> [ [ mylastcdr ] (call) ] (call) ; ! Works well

    ! seems to work with all combinations...
    ! cdr>> mylastcdr ;

M: +nil+ mylastcdr ;
! M: object mylastcdr ;
! M: array mylastcdr 2 slot [ mylastcdr ] (call) ;
TYPED: array-first ( arr: array -- thing ) 2 slot ;
! M: array mylastcdr array-first mylastcdr ;
M: array mylastcdr array-first [ [ mylastcdr ] ] (call) (call) ;
! M: array mylastcdr array-first [ [ mylastcdr ] (call) ] (call) ;

! Needs make-unit recursion resolution in some form...
: myloop ( -- ) [ call ] keep swap [ myloop ] [ drop ] if ; inline recursive

: get-type ( quot -- type )
    [ qt values [ TypeOf? ] filter ]
    [ [ swap thing>> = ] curry find nip ] bi
    dup [ type>> ] when ;

{ t } [ [ myloop ] get-type dup [ full-type? ] when ] unit-test

GENERIC: lastcdr1 ( list -- obj )
M: list lastcdr1 cdr>> lastcdr1 ;
M: +nil+ lastcdr1 ;

TERM-VARS: ?a15 ?y1 ?ys1 ?b3 ?b4 ?o3 ?v3 ;

CONSTANT: sol1
P{
    Xor
    P{ Effect L{ ?y1 . ?ys1 } L{ ?y1 . ?ys1 } { ?y1 } { P{ Instance ?y1 L{ } } } }
    P{ Effect L{ ?o3 . ?a15 } ?b4 { ?o3 } { P{ CallRecursive __ L{ ?v3 . ?a15 } ?b4 } P{ Instance ?o3 cons-state } P{ Slot ?o3 "cdr" ?v3 } } }
}
! P{
!     Xor
!     P{ Effect ?a3 ?a3 f { P{ Declare L{ L{ } } ?a3 } } }
!     P{
!         Effect
!         L{ ?o3 . ?a11 }
!         ?b3 f
!         { P{ CallRecursive __ L{ ?v3 . ?a11 } ?b3 } P{ Instance ?o3 cons-state } P{ Slot ?o3 "cdr" ?v3 } }
!     }
! }

{ t }
[ [ lastcdr1 ] get-type sol1 isomorphic? ] unit-test

GENERIC: lastcdr2 ( list -- obj )
M: list lastcdr2 cdr>> [ lastcdr2 ] (call) ;
M: +nil+ lastcdr2 ;

{ t }
[ [ lastcdr2 ] get-type sol1 isomorphic? ] unit-test

GENERIC: lastcdr3 ( list -- obj )
M: list lastcdr3 cdr>> [ [ lastcdr3 ] ] (call) (call) ;
M: +nil+ lastcdr3 ;

{ t }
[ [ lastcdr3 ] get-type sol1 isomorphic? ] unit-test

{ t }
[ [ [ lastcdr3 ] (call) ] get-type sol1 isomorphic? ] unit-test

{ t }
[ [ [ [ lastcdr3 ] ] (call) (call) ] get-type sol1 isomorphic? ] unit-test

GENERIC: lastcdr5 ( list -- obj )
M: list lastcdr5 cdr>> lastcdr5 ;
M: +nil+ lastcdr5 ;
M: array lastcdr5 array-first lastcdr5 ;

{ t }
[ [ lastcdr5 ] get-type dup [ full-type? ] when ] unit-test

GENERIC: lastcdr4 ( list -- obj )
M: list lastcdr4 cdr>> [ [ lastcdr4 ] ] (call) (call) ;
M: +nil+ lastcdr4 ;
M: array lastcdr4 array-first lastcdr4 ;

{ t }
[ [ lastcdr4 ] get-type dup [ full-type? ] when ] unit-test

{ t }
[ [ lastcdr4 ] get-type [ [ lastcdr4 ] (call) ] get-type isomorphic? ] unit-test

! NOTE: This one does not work because we don't recursively perform full phi-computations
! through multiple levels of nested effects
! { t }
{ f }
[ [ [ lastcdr5 ] ] get-type [ [ [ lastcdr5 ] ] (call) ] get-type isomorphic? ] unit-test

! Stack checker examples
: bad ( ? quot: ( ? -- ) -- ) 2dup [ not ] dip bad call ; inline recursive
: good ( ? quot: ( ? -- ) -- ) [ good ] 2keep [ not ] dip call ; inline recursive

! ** Practical examples

PREDICATE: u8 < integer { [ 0 >= ] [ 256 < ] } 1&& ;
