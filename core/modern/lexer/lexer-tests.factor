! Copyright (C) 2016 Doug Coleman.
! See http://factorcode.org/license.txt for BSD license.
USING: tools.test modern.lexer ;
in: modern.lexer.tests

{ T{ slice f 0 8 "dinosaur" } f } [
    "dinosaur" <modern-lexer> lex-til-whitespace [ drop ] 2dip
] unit-test

{ f f } [
    "dinosaur" <modern-lexer>
    [ lex-til-whitespace 2drop ] [ lex-til-whitespace ] bi [ drop ] 2dip
] unit-test