! Copyright (C) 2016 Doug Coleman.
! See http://factorcode.org/license.txt for BSD license.
USING: accessors constructors kernel math sequences
sequences.extras slots.syntax ;
in: modern.lexer

TUPLE: modern-lexer n string stack ;
CONSTRUCTOR: <modern-lexer> modern-lexer ( string -- obj )
    0 >>n
    V{ } clone >>stack ; inline

: >lexer< ( lexer -- n string ) slots[ n string ] ;

:: slice-til-either ( n string tokens -- n'/f string slice/f ch/f )
    n [
        n string '[ tokens member? ] find-from
        dup "\s\r\n" member? [
            :> ( n' ch )
            n' string
            n n' string ?<slice>
            ch
        ] [
            [ dup [ 1 + ] when ] dip :> ( n' ch )
            n' string
            n n' string ?<slice>
            ch
        ] if
    ] [
        f string f f
    ] if ; inline

:: lex-til-either ( lexer tokens -- lexer slice/f ch/f )
    lexer >lexer< tokens slice-til-either :> ( n' string' slice ch )
    lexer
        n' >>n
    slice ch ;


:: slice-til-separator-inclusive ( n string tokens -- n' string slice/f ch/f )
    n string '[ tokens member? ] find-from [ dup [ 1 + ] when ] dip  :> ( n' ch )
    n' string
    n n' string ?<slice>
    ch ; inline

:: lex-til-separator-inclusive ( lexer tokens -- lexer slice/f ch/f )
    lexer >lexer< tokens slice-til-separator-inclusive :> ( n' string' slice ch )
    lexer
        n' >>n
    slice ch ;


: slice-til-separator-exclusive ( n string tokens -- n' string slice/f ch/f )
    slice-til-separator-inclusive dup [
        [ [ 1 - ] change-to ] dip
    ] when ;

:: lex-til-separator-exclusive ( lexer tokens -- lexer slice/f ch/f )
    lexer >lexer< tokens slice-til-separator-exclusive :> ( n' string' slice ch )
    lexer
        n' >>n
    slice ch ;

! Don't include the whitespace in the slice
:: slice-til-whitespace ( n string -- n'/f string slice/f ch/f )
    n [
        n string [ "\s\r\n" member? ] find-from :> ( n' ch )
        n' string
        n n' string ?<slice>
        ch
    ] [
        f string f f
    ] if ; inline

:: lex-til-whitespace ( lexer -- lexer slice/f ch/f )
    lexer >lexer< slice-til-whitespace :> ( n' string' slice ch )
    lexer
        n' >>n
    slice ch ;


: merge-lex-til-whitespace ( lexer slice --  lexer slice' )
    [ lex-til-whitespace drop ] dip merge-slices ;


:: slice-til-eol ( n string -- n'/f string slice/f ch/f )
    n [
        n string '[ "\r\n" member? ] find-from :> ( n' ch )
        n' string
        n n' string ?<slice>
        ch
    ] [
        f string f f
    ] if ; inline

:: lex-til-eol ( lexer -- lexer slice/f ch/f )
    lexer >lexer< slice-til-eol :> ( n' string' slice ch )
    lexer
        n' >>n
    slice ch ;


ERROR: subseq-expected-but-got-eof n string expected ;

:: slice-til-string ( n string search --  n' string payload closing )
    search string n start* :> n'
    n' [ n string search subseq-expected-but-got-eof ] unless
    n' search length +  string
    n n' string ?<slice>
    n' dup search length + string ?<slice> ;

:: lex-til-string ( lexer search -- lexer payload closing )
    lexer >lexer< search slice-til-string :> ( n' string' payload closing )
    lexer
        n' >>n
    payload closing ;
