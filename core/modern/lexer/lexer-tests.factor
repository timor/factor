! Copyright (C) 2016 Doug Coleman.
! See http://factorcode.org/license.txt for BSD license.
USING: kernel modern.lexer sequences tools.test ;
IN: modern.lexer.tests

![[
{ T{ slice f 0 8 "dinosaur" } f } [
    "dinosaur" <modern-lexer> lex-til-whitespace
] unit-test

{ f f } [
    "dinosaur" <modern-lexer>
    [ lex-til-whitespace 2drop ] [ lex-til-whitespace ] bi
] unit-test
]]
