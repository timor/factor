USING: chr.factor chr.parser kernel sequences tools.test ;
IN: chr.factor.tests

! { 3 3 }
! [
!     ( ..a cond: boolean then: ( ..a1 -- ..b1 ) else: ( ..a2 -- ..b2 ) -- ..b )
!     dup define-term-vars make-interface-constraints
!     [ [ Val? ] count ]
!     [ [ Instance? ] count ] bi
! ] unit-test

! : my-if ( cond then else -- )
!     if ; inline

! CONSTRAINT: if basic ( ..a cond: boolean then: ( ..a1 -- ..b1 ) else: ( ..a2 -- ..b2 ) -- ..b )
! CHR{ { Word a b if } // -- | gen{ "strue" "sfalse" |
!                                   { Dispatch a a1 cond "strue" }
!                                   { Dispatch a a2 cond "sfalse" }
!                                   { Join b1 b cond }
!                                   { Join b2 b cond }
!                                   { InferUnknown a1 b1 then }
!                                   { InferUnknown b1 b2 then }
!                                 } }
!     ; drop
