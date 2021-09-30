USING: effects kernel math tools.test types.renaming ;
IN: types.renaming.tests


! TODO: resurrect with terms if necessary
! { "( ..r0 quot0: ( ...0 a0 -- ...0 b0 ) -- ..r0 quot1 )" }
! [ ( quot: ( ... a -- ... b ) -- quot0 ) name>vars effect>string ] unit-test

! { "( ..r1 quot0: ( ..r0 -- ..r0 ) quot0: ( ..r2 a0 -- ..r2 b0 ) -- ..r1 quot1 )" }
! [ ( ..r1 quot: ( -- ) quot: ( a -- b ) -- ..r1 quot0 ) name>vars effect>string ] unit-test

! { "( ..r0 quot0: ( ..r1 a0 -- ..r1 b0 ) -- ..r0 quot1 )" }
! [ ( quot: ( ..r0 a -- ..r0 b ) -- quot0 ) name>vars effect>string ] unit-test

! { "( ..r0 -- ..r0 x0: integer y0: fixnum )" }
! [ ( ..r -- ..r x: integer y: fixnum ) name>vars effect>string ] unit-test

! { "( ..r0 -- ..r0 )"
!   "( ..r1 quot0: ( ...0 a0 -- ...0 b0 ) -- ..r1 quot1 )" }
! [ ( -- ) ( quot: ( ... a -- ... b ) -- quot0 ) rename-effects [ effect>string ] bi@ ] unit-test

! { "( ..r0 -- ..r0 )"
!   "( ..r1 quot0: ( ..r2 a0 -- ..r2 b0 ) -- ..r1 quot1 )" }
! [ ( -- ) ( quot: ( ..r0 a -- ..r0 b ) -- quot0 ) rename-effects [ effect>string ] bi@ ] unit-test

! { "( ..r0 -- ..r0 x0: integer y0: fixnum )"
!   "( ..r1 -- ..r1 x1: integer y1: fixnum )" }
! [ ( ..r -- ..r x: integer y: fixnum ) dup rename-effects [ effect>string ] bi@ ] unit-test

! { "( ..r0 -- ..r0 quot0: ( ..r1 -- ..r1 ) )" }
! [ ( -- quot: ( -- ) ) name>vars effect>string ] unit-test

! { "( ..a0 b0 quot0: ( ..a0 -- ..c0 ) quot2: ( ..c0 b0 -- ..b0 ) -- ..b0 )" }
! [ ( ..a b quot: ( ..a -- ..c ) quot2: ( ..c b -- ..b ) -- ..b )
!   name>vars effect>string ] unit-test

! { "( ..a0 x0 quot0: ( ..a0 -- ..c0 ) quot0: ( ..c0 x0 -- ..b0 ) -- ..b0 )" }
! [ ( ..a x quot: ( ..a -- ..c ) quot: ( ..c x -- ..b ) -- ..b ) name>vars effect>string ] unit-test

! { "( ..a0 b0 quot0: ( ..a0 -- ..c0 ) quot0: ( ..c0 b0 -- ..b0 ) -- ..b0 )" }
! [ ( ..a b quot: ( ..a -- ..c ) quot: ( ..c b -- ..b ) -- ..b ) name>vars effect>string ] unit-test
