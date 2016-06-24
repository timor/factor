! Copyright (C) 2008, 2009 Slava Pestov.
! See http://factorcode.org/license.txt for BSD license.
USING: combinators compiler.units continuations debugger
effects.parser io.streams.string kernel kernel.private multiline
namespaces parser parser.notes sequences splitting ;
IN: eval

: parse-string ( str -- quot )
    [ string-lines parse-lines ] with-compilation-unit ;

: (eval) ( str effect -- )
    [ parse-string ] dip call-effect ; inline

: eval ( str effect -- )
    [ (eval) ] with-file-vocabs ; inline

SYNTAX: \ eval( \ eval parse-call-paren ;

SYNTAX: \ eval[[
    "]]" parse-multiline-string
    '[ get-datastack _ parse-string with-datastack set-datastack ] append! ;

: (eval>string) ( str -- output )
    [
        parser-quiet? on
        '[ _ ( -- ) (eval) ] [ print-error ] recover
    ] with-string-writer ;

: eval>string ( str -- output )
    [ (eval>string) ] with-file-vocabs ;
