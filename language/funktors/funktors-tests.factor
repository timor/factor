! Copyright (C) 2016 Doug Coleman.
! See http://factorcode.org/license.txt for BSD license.
USING: funktors math tools.test ;
IN: funktors.tests

COMPILE<

FUNKTOR: define-box ( T -- ) [[
TUPLE: ${T}-box { value ${T} } ;
C: <${T}-box> ${T}-box
]]

\ float define-box

COMPILE>

{ 1 0 } [ define-box ] must-infer-as

[ T{ float-box f 5.0 } ] [ 5.0 <float-box> ] unit-test
