USING: math fry macros eval tools.test ;
IN: compiler.tests.redefine13

: breakage-word ( a b -- c ) + ;

COMPILE< MACRO: breakage-macro ( a -- quot ) $[ _ breakage-word ] ; COMPILE>

GENERIC: breakage-caller ( a -- c ) ;

M: fixnum breakage-caller 2 breakage-macro ;

: breakage ( -- obj ) 2 breakage-caller ;

! [ ] [ "IN: compiler.tests.redefine13 : breakage-word ( a b -- c ) ;" eval ] unit-test
