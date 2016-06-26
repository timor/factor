! Copyright (C) 2007 Daniel Ehrenberg
! See http://factorcode.org/license.txt for BSD license.
USING: accessors kernel lexer make math namespaces sequences ;
IN: multiline

PRIVATE<

:: scan-multiline-string ( i end lexer -- j )
    lexer line-text>> set: text
    lexer still-parsing? [
        end text i start* |[ j |
            i j text subseq % j end length +
        ] [
            text i short tail % char: \n ,
            lexer next-line
            0 end lexer scan-multiline-string
        ] if*
    ] [ end throw-unexpected-eof ] if ;

:: (parse-multiline-string) ( end-text lexer skip-n-chars -- str )
    [
        lexer
        [ skip-n-chars + end-text lexer scan-multiline-string ]
        change-column drop
    ] "" make ;

PRIVATE>


: parse-multiline-string-old ( end-text -- str )
    lexer get 1 (parse-multiline-string) ;

: parse-multiline-string-new ( end-text -- str )
    lexer get 0 (parse-multiline-string) ;

: parse-multiline-string ( end-text -- str )
    parse-multiline-string-old ;

SYNTAX: /* "*/" parse-multiline-string drop ;
