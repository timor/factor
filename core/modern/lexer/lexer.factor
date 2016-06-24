! Copyright (C) 2016 Doug Coleman.
! See http://factorcode.org/license.txt for BSD license.
USING: accessors constructors kernel math sequences
sequences.extras slots.syntax unicode ;
IN: modern.lexer

TUPLE: modern-lexer n string partial stack ;
CONSTRUCTOR: <modern-lexer> modern-lexer ( string -- obj )
    0 >>n
    V{ } clone >>stack ; inline

: >lexer< ( lexer -- n string ) slots[ n string ] ;

: ?lexer-nth ( lexer -- obj )
    >lexer< over [ ?nth ] [ 2drop f ] if ;

: lexer-eof? ( lexer -- obj )
    n>> >boolean ;

: push-tag ( lexer tag -- )
    swap stack>> push ;

: peek-tag ( lexer -- tag )
    stack>> ?last ;

: pop-tag ( lexer -- )
    stack>> pop drop ;

: with-tag ( lexer tag quot -- )
    [ [ push-tag ] dip call ] 3keep 2drop pop-tag ; inline

: roll-back-lexer ( lexer slice -- )
    from>> >>n drop ;

ERROR: unexpected-end n string ;
: nth-check-eof ( n string -- nth )
    2dup ?nth [ 2nip ] [ unexpected-end ] if* ; inline

: lexer-nth-check-eof ( lexer -- nth )
    >lexer< nth-check-eof ;

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

! ":foo" with partial>> slot broke this
:: lex-til-either ( lexer tokens -- n'/f string' slice/f ch/f )
    lexer >lexer<
    lexer partial>> :> partial
    partial [
        [ dup [ 1 - ] when ] dip
        f lexer partial<<
    ] when
    tokens slice-til-either :> ( n' string' slice ch )
    lexer
        n' >>n drop
    n' string'
    slice partial 2dup and [ merge-slices ] [ or ] if
    ch ;


:: slice-til-separator-inclusive ( n string tokens -- n' string slice/f ch/f )
    n string '[ tokens member? ] find-from [ dup [ 1 + ] when ] dip  :> ( n' ch )
    n' string
    n n' string ?<slice>
    ch ; inline

:: lex-til-separator-inclusive ( lexer tokens -- n' string' slice/f ch/f )
    lexer >lexer< tokens slice-til-separator-inclusive :> ( n' string' slice ch )

    lexer
        n' >>n drop

    n' string' slice ch ;


: slice-til-separator-exclusive ( n string tokens -- n' string slice/f ch/f )
    slice-til-separator-inclusive dup [
        [ [ 1 - ] change-to ] dip
    ] when ;

:: lex-til-separator-exclusive ( lexer tokens -- n'/f string' slice/f ch/f )
    lexer >lexer< tokens slice-til-separator-exclusive :> ( n' string' slice ch )
    lexer
        n' >>n drop
    n' string' slice ch ;

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

:: lex-til-whitespace ( lexer -- n'/f string slice/f ch/f )
    lexer >lexer< slice-til-whitespace :> ( n' string' slice ch )
    lexer
        n' >>n drop
    n' string' slice ch ;

! rollback only n, other state is not rolled back
:: with-lexer-rollback ( lexer quot -- )
    lexer n>> :> n
    lexer quot call lexer n >>n drop ; inline


: merge-lex-til-whitespace ( lexer slice --  slice' )
    [ lex-til-whitespace drop 2nip ] dip merge-slices ;

: peek-merge-til-whitespace ( lexer slice -- slice' )
    '[ _ merge-lex-til-whitespace ] with-lexer-rollback ;

:: slice-til-eol ( n string -- n'/f string slice/f ch/f )
    n [
        n string '[ "\r\n" member? ] find-from :> ( n' ch )
        n' string
        n n' string ?<slice>
        ch
    ] [
        f string f f
    ] if ; inline

:: lex-til-eol ( lexer -- n' string' slice/f ch/f )
    lexer >lexer< slice-til-eol :> ( n' string' slice ch )
    lexer
        n' >>n drop
    n' string' slice ch ;


ERROR: subseq-expected-but-got-eof n string expected ;

:: slice-til-string ( n string search --  n' string payload closing )
    search string n start* :> n'
    n' [ n string search subseq-expected-but-got-eof ] unless
    n' search length +  string
    n n' string ?<slice>
    n' dup search length + string ?<slice> ;

:: lex-til-string ( lexer search -- n'/f string' payload closing )
    lexer >lexer< search slice-til-string :> ( n' string' payload closing )
    lexer
        n' >>n drop
    n' string' payload closing ;


: find-from* ( ... n seq quot: ( ... elt -- ... ? ) -- ... i elt ? )
    [ find-from ] keep
    pick [ drop t ] [ length -rot nip f ] if ; inline

: skip-blank-from ( n string -- n' string )
    [ [ blank? not ] find-from* 2drop ] keep ; inline

: skip-blanks ( lexer -- lexer )
    dup >lexer< skip-blank-from drop >>n ; inline

ERROR: char-expected-but-got-eof n string expected ;

:: slice-til-not-char ( n string slice char --  n' string found )
    n string [ char = not ] find-from drop :> n'
    n' [ n string char char-expected-but-got-eof ] unless
    n'
    string
    slice from>> n' string ?<slice> ;

:: lex-til-not-char ( lexer slice char -- n'/f string' found )
    lexer >lexer< slice char slice-til-not-char :> ( n' string' found )
    lexer
        n' >>n drop
    n' string' found ;
