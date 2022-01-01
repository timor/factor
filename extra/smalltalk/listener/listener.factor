! Copyright (C) 2009 Slava Pestov.
! See http://factorcode.org/license.txt for BSD license.
USING: kernel prettyprint io io.styles colors compiler.units
fry debugger sequences locals.rewrite smalltalk.ast
smalltalk.eval smalltalk.printer smalltalk.listener splitting ;
IN: smalltalk.listener

: eval-interactively ( string -- )
    '[
        _ eval-smalltalk
        dup nil? [ drop ] [ "Result: " write smalltalk>string print ] if
    ] try ;

: smalltalk-listener ( -- )
    "Smalltalk>" { { background COLOR: light-blue } } format bl flush readln
    [ eval-interactively smalltalk-listener ] when* ;

MAIN: smalltalk-listener
