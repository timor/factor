! Copyright (C) 2010 John Benediktsson
! See http://factorcode.org/license.txt for BSD license
USING: colors colors.hex tools.test ;

{ hexcolor: 000000 } [ 0.0 0.0 0.0 1.0 <rgba> ] unit-test
{ hexcolor: FFFFFF } [ 1.0 1.0 1.0 1.0 <rgba> ] unit-test
{ hexcolor: abcdef } [ "abcdef" hex>rgba ] unit-test
{ hexcolor: abcdef } [ "ABCDEF" hex>rgba ] unit-test
{ "ABCDEF" } [ hexcolor: abcdef rgba>hex ] unit-test
