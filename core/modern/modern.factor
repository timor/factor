! Copyright (C) 2016 Doug Coleman.
! See http://factorcode.org/license.txt for BSD license.
USING: accessors arrays assocs assocs.extras combinators
combinators.short-circuit constructors continuations fry
generalizations io.encodings.utf8 io.files kernel locals macros
make math math.order modern.lexer modern.paths modern.slices
namespaces quotations sequences sequences.extras
shuffle splitting splitting.extras splitting.monotonic strings
unicode vocabs.loader ;
IN: modern

COMPILE<
! Base rules, everything should have a generator macro
TUPLE: lexer generator ;

! Declarative rules, add more!
TUPLE: tag-lexer < lexer ; ! default, if nothing else matches, add one with regexp for c-style names etc
TUPLE: dquote-lexer < lexer delimiter escape ignore-whitespace? ; ! ``close`` slot someday to allow ` '
TUPLE: matched-lexer < lexer delimiter double-char ; ! ``close`` slot someday, to allow `` ''
TUPLE: less-than-lexer < lexer delimiter double-char ; ! ``close`` slot someday, to allow `` ''
TUPLE: backtick-lexer < lexer delimiter ;
TUPLE: backslash-lexer < lexer delimiter payload-exception? ; ! payload-exception is \n words
TUPLE: line-comment-lexer < lexer delimiter word-name-exception? ; ! escape-newline-exception? (like C)
TUPLE: colon-lexer < lexer delimiter ;
TUPLE: semicolon-lexer < lexer delimiter ; ! ; inline foldable
TUPLE: whitespace-lexer < lexer delimiter ; ! \s \r \n \t?
TUPLE: terminator-lexer < lexer delimiter ;
TUPLE: decorator-lexer < lexer delimiter ;

! Base lexer result
TUPLE: literal underlying seq lexer left-decorators right-decorators ;
TUPLE: tag-literal < literal tag ;
TUPLE: matched-literal < tag-literal delimiter payload closing-tag ;
TUPLE: delimited-literal < tag-literal delimiter payload ;
TUPLE: decorator-literal < literal delimiter payload ;

TUPLE: dquote-literal < matched-literal ;
TUPLE: single-matched-literal < matched-literal ;
TUPLE: double-matched-literal < matched-literal ;
TUPLE: less-than-literal < single-matched-literal ;
TUPLE: uppercase-colon-literal < single-matched-literal ;
TUPLE: lowercase-colon-literal < delimited-literal ;
! TUPLE: standalone-colon-literal < delimited-literal ; ! :foo
TUPLE: backtick-literal < delimited-literal ;
TUPLE: backslash-literal < delimited-literal ;
TUPLE: semicolon-literal < delimited-literal ;
TUPLE: line-comment-literal < delimited-literal ;
TUPLE: terminator-literal < tag-literal ;
TUPLE: whitespace-literal < tag-literal ;

TUPLE: left-decorator-literal < decorator-literal ;
TUPLE: right-decorator-literal < decorator-literal ;

TUPLE: compound-sequence-literal sequence ;
CONSTRUCTOR: <compound-sequence-literal> compound-sequence-literal ( sequence -- obj ) ;
COMPILE>

GENERIC: lexed-underlying ( obj -- slice ) ;
M: f lexed-underlying ;
M: object lexed-underlying underlying>> ;
M: slice lexed-underlying ;

TUPLE: compound-literal sequence ;
CONSTRUCTOR: <compound-literal> compound-literal ( sequence -- obj ) ;

! Ensure that we only have one decorated thing in a compound-literal
ERROR: bad-compound-literal seq decorators words ;
: check-compound-literal ( seq -- seq ) ;

GENERIC: make-compound-literals ( seq -- seq' ) ;
M: object make-compound-literals ;
M: array make-compound-literals
    [
        {
            [ [ lexed-underlying ] bi@ slices-touch? ]
            [ [ ] [ left-decorator-literal? ] bi* and ]
            [ [ right-decorator-literal? ] [ ] bi* and ]
        } 2||
    ] monotonic-split
    [ dup length 1 > [ <compound-literal> ] [ first ] if ] map ;

! We have empty decorators, just the @ right here
! wrap the decorated object in the payload slot
GENERIC: collapse-decorators ( seq -- seq' ) ;
M: object collapse-decorators ;
M: array collapse-decorators
    [
        {
            [ [ left-decorator-literal? ] [ ] bi* and ]
            [ [ ] [ right-decorator-literal? ] bi* and ]
        } 2||
    ] monotonic-split
    [
        dup length 1 > [
            first2
            2dup [ left-decorator-literal? ] [ ] bi* and [
                >>payload
            ] [
                [ payload<< ] keep
            ] if
        ] [
            first
        ] if
    ] map ;

: split-double-dash ( seq -- seqs )
    dup [ { [ tag-literal? ] [ tag>> "--" = ] } 1&& ] split*-when
    dup length 1 > [
        nip <compound-sequence-literal>
    ] [
        drop
    ] if ;

: postprocess-lexed ( seq -- seq' )
    collapse-decorators make-compound-literals ;

! foo:bar-baz09:
: strict-upper-letter? ( ch -- ? )
    { [ char: A char: Z between? ] [ char: 0 char: 9 between? ] [ ":-#" member? ] } 1|| ;

: strict-upper? ( string -- ? )
    [ strict-upper-letter? ] all? ;

: whitespace/f? ( ch -- ? )
    { char: \s char: \r char: \n f } member? ; inline

: scoped-colon-name ( string -- string' )
    dup [ length 2 - ] keep [ char: \: = ] find-last-from [ 1 + tail ] [ drop ] if ;

: scoped-less-than-name ( string -- string' )
    dup [ length 2 - ] keep [ char: < = ] find-last-from [ 1 + tail ] [ drop ] if ;

: trim-top-level ( string -- string' )
    {
        { [ dup "<" tail? ] [ but-last ] }
        { [ dup ":" tail? ] [ [ char: \: = ] trim-tail ] }
        [ ]
    } cond ;

: top-level-colon? ( string -- ? )
    dup ":" tail? [
        dup length 1 > [
            [ trim-top-level [ char: \: = ] find-last ] keep
            swap [ swap tail strict-upper? ] [ nip strict-upper? ] if
        ] [
            ":" sequence=
        ] if
    ] [
        drop f
    ] if ;

: top-level-less-than? ( string -- ? )
    dup { [ "<" tail? ] [ length 1 > ] [ first char: A char: Z between? ] } 1&& [
        but-last
        dup length 1 > [
            [ [ char: \: = ] find-last ] keep
            swap [ swap tail strict-upper? ] [ nip strict-upper? ] if
        ] [
            [ char: \< = ] all? not
        ] if
    ] [
        drop f
    ] if ;

: top-level-greater-than? ( string -- ? )
    dup { [ ">" tail? ] [ length 1 > ] [ first char: A char: Z between? ] } 1&& [
        but-last
        dup length 1 > [
            [ [ char: \: = ] find-last ] keep
            swap [ swap tail strict-upper? ] [ nip strict-upper? ] if
        ] [
            [ char: \> = ] all? not
        ] if
    ] [
        drop f
    ] if ;

: top-level-name? ( string -- ? )
    { [ top-level-colon? ] [ top-level-less-than? ] } 1|| ;

ERROR: no-start-delimiter lexer opening ;
:: delimiters-match? ( lexer opening closing -- ? )
    opening empty? [ lexer opening closing no-start-delimiter ] when

    opening 1 cut* over empty? [
        nip matching-delimiter-string 1array
    ] [
        matching-delimiter-string [ append ] [ nip ] 2bi 2array
    ] if closing '[ _ sequence= ] any? ;


ERROR: whitespace-expected-after n string ch ;
ERROR: expected-more-tokens n string expected ;
ERROR: string-expected-got-eof n string ;

:: make-tag-literal ( tag -- literal )
    tag-literal new
        tag >string >>tag
        tag >>underlying
        tag 1array >>seq ; inline

:: make-tag-class-literal ( tag class -- literal )
    class new
        tag >string >>tag
        tag >>underlying
        tag 1array >>seq ; inline

:: make-tag-payload-literal ( payload last tag class -- literal )
    class new
        tag >string >>tag
        payload >string >>payload
        tag last [ dup tag-literal? [ lexed-underlying ] when ] bi@ ?span-slices >>underlying
        tag payload 2array >>seq ; inline

:: make-delimited-literal ( payload last tag delimiter class -- literal )
    class new
        tag >string >>tag
        payload dup slice? [ >string ] when >>payload
        tag last [ dup tag-literal? [ lexed-underlying ] when ] bi@ ?span-slices >>underlying
        delimiter >string >>delimiter
        tag delimiter payload 3array >>seq ; inline

ERROR: closing-delimiter-required opening-delimiter ;
:: make-matched-literal ( payload closing tag opening-delimiter class -- literal )
    class new
        tag >string >>tag
        payload postprocess-lexed opening-delimiter "\"" = [ split-double-dash ] unless >>payload
        tag closing [ dup tag-literal? [ lexed-underlying ] when ] bi@ ?span-slices >>underlying
        opening-delimiter >string >>delimiter

        closing dup tag-literal? [ tag>> ] when >string f like >>closing-tag

        ! PRIVATE< PRIVATE>
        dup less-than-literal? [
            closing f = [ opening-delimiter closing-delimiter-required ] when
        ] when
        tag opening-delimiter payload closing 4array >>seq ; inline

:: make-decorator-literal ( payload delimiter class -- literal )
    class new
        delimiter >>delimiter
        payload >>payload
        payload delimiter [ lexed-underlying ] bi@ ?span-slices >>underlying
        class left-decorator-literal = [
            delimiter payload 2array
        ] [
            payload delimiter 2array
        ] if >>seq ; inline

:: make-decorator-sentinel ( delimiter left? -- literal )
    left? left-decorator-literal right-decorator-literal ? new
        delimiter >>delimiter
        delimiter 1array >>seq
        delimiter >>underlying ; inline

ERROR: long-opening-mismatch tag open lexer ch ;

! (( )) [[ ]] {{ }}
MACRO:: read-double-matched ( open-ch -- quot: ( lexer tag ch -- seq ) )
    open-ch dup matching-delimiter {
        [ drop 2 swap <string> ]
        [ drop 1string ]
        [ nip 2 swap <string> ]
    } 2cleave :> ( openstr2 openstr1 closestr2 )
    |[ lexer tag! ch |
        ch {
            { char: = [
                lexer openstr1 lex-til-separator-inclusive [ -1 modify-from ] dip :> ( n' string' opening ch )
                ch open-ch = [ tag openstr2 lexer ch long-opening-mismatch ] unless
                opening matching-delimiter-string :> needle

                lexer needle lex-til-string :> ( n'' string'' payload closing )
                payload closing tag but-last-slice opening double-matched-literal make-matched-literal
                [ >string ] change-payload
            ] }
            { open-ch [
                tag 1 cut-slice* swap tag! 1 modify-to :> opening
                lexer [ 1 + ] change-n closestr2 lex-til-string :> ( n' string' payload closing )
                payload closing tag opening double-matched-literal make-matched-literal
                [ >string ] change-payload
            ] }
            [ [ tag openstr2 lexer ] dip long-opening-mismatch ]
        } case
     ] ;

: read-double-matched-paren ( lexer tag ch -- seq ) char: \( read-double-matched ;
: read-double-matched-bracket ( lexer tag ch -- seq ) char: \[ read-double-matched ;
: read-double-matched-brace ( lexer tag ch -- seq ) char: \{ read-double-matched ;

DEFER: lex
DEFER: lex-factor

! make lex-top-level and lex-matched
! lex-top-level lexes til FOO; ; or TAG:, on TAG: leave n' at start of TAG:
! lex-matched lexes til foo) foo} foo] ) } ] or TAG:, on TAG: throw error


ERROR: lex-expected-but-got-eof lexer tags ;

ERROR: unnestable-form n string obj ;
! For implementing [ { (
: lex-until ( lexer tags -- payload closing )
    '[
        [
            _ lex-factor [
                dup tag-literal? [
                    dup ,
                    underlying>> _ [ sequence= ] with any? not
                ] [ , t ] if
            ] [
                f , f
            ] if*
        ] loop
    ] { } make unclip-last ; inline

MACRO:: read-matched ( ch -- quot: ( lexer tag -- slice' ) )
    ch dup matching-delimiter {
        [ drop "=" swap prefix ]
        [ nip 1string ]
    } 2cleave :> ( openstreq closestr1 )  ! [= ]

    |[ lexer tag |
        lexer tag
        over lexer-nth-check-eof {
            { [ dup openstreq member? ] [ ch read-double-matched ] } ! (=( or ((
            { [ dup blank? ] [
                drop dup '[
                    _ matching-delimiter-string closestr1
                    2dup = [ drop 1array ] [ 2array ] if lex-until
                ] dip 1 cut-slice* single-matched-literal make-matched-literal
            ] } ! ( foo )
            [ drop [ lex-til-whitespace drop 2nip ] dip span-slices make-tag-literal ]  ! (foo)
        } cond
    ] ;

: read-bracket ( lexer slice -- slice' ) 2dup [ char: \[ read-matched ] with-tag ;
: read-brace ( lexer slice -- slice' ) 2dup [ char: \{ read-matched ] with-tag ;
: read-paren ( lexer slice -- slice' ) 2dup [ char: \( read-matched ] with-tag ;

:: read-string-payload ( lexer -- n' string slice )
    lexer dup ?lexer-nth [
        { char: \\ char: \" } lex-til-separator-inclusive :> ( n' string' slice ch )
        ch {
            { f [ n' string' slice ] }
            { char: \" [ n' string' slice ] }
            { char: \\ [ lexer [ 1 + ] change-n read-string-payload ] }
        } case
    ] [
        lexer >lexer< f string-expected-got-eof
    ] if ;

:: read-string ( lexer tag -- seq )
    lexer n>> :> n
    lexer read-string-payload :> ( n' string slice )
    n' [ n string string-expected-got-eof ] unless
    n n' 1 - string <slice>
    n' 1 - n' string <slice>
    tag 1 cut-slice* dquote-literal make-matched-literal
    [ >string ] change-payload ;

ERROR: cannot-nest-upper-colon n string string' ;
: read-upper-colon ( lexer string' -- obj/f )
    over peek-tag top-level-colon? [
        roll-back-lexer f
    ] [
        2dup [
            dup [
                [ but-last ";" append ";" 2array ] [ ";" 1array ] if* lex-until
            ] dip 1 cut-slice* uppercase-colon-literal make-matched-literal
        ] with-tag
    ] if ;

: read-lower-colon ( lexer string' -- obj )
    [ lex-factor dup ] dip 1 cut-slice*
    lowercase-colon-literal make-delimited-literal ;

! : foo: :foo foo:bar foo:BAR: foo:bar: :foo:
: read-colon ( lexer slice -- colon )
    dupd merge-lex-til-whitespace {
        { [ dup length 1 = ] [ read-upper-colon ] }
        { [ dup [ char: \: = ] all? ] [ read-upper-colon ] }
        { [ dup { [ ":" head? ] [ ":" tail? ] } 1&& ] [ nip make-tag-literal ] }
        { [ dup ":" tail? ] [ dup top-level-name? [ read-upper-colon ] [ read-lower-colon ] if ] }
        { [ dup ":" head? ] [ >>partial lex-factor ] } ! :foo( ... )
        [ nip make-tag-literal ]
    } cond ;


ERROR: closing-tag-required lexer tag ;

:: read-upper-less-than ( lexer slice -- less-than/f )
    lexer peek-tag top-level-colon? [
        lexer slice roll-back-lexer f
    ] [
        lexer slice [
            lexer slice scoped-less-than-name but-last ">" append 1array lex-until
            ! dup [ lexer slice >string closing-tag-required ] unless
            slice 1 cut-slice* less-than-literal make-matched-literal
        ] with-tag
    ] if ;

: read-less-than ( lexer slice -- less-than )
    dupd merge-lex-til-whitespace {
        { [ dup "<" tail? ] [ dup top-level-name? [ read-upper-less-than ] [ nip make-tag-literal ] if ] } ! FOO< or foo<
        [ >>partial lex-factor ]
    } cond ;


: take-comment ( lexer slice -- comment )
    over ?lexer-nth char: \[ = [
        [ [ 1 + ] change-n ] [ 1 modify-to ] bi*
        over ?lexer-nth read-double-matched-bracket
    ] [
        [ lex-til-eol drop 2nip dup ] dip 1 cut-slice* line-comment-literal make-delimited-literal
    ] if ;

! Words like append! and suffix! are allowed for now.
: read-exclamation ( lexer slice -- obj )
    dup { [ "!" sequence= ] [ "#!" sequence= ] } 1||
    [ take-comment ] [ >>partial [ 1 + ] change-n lex-factor ] if ;


: read-backtick ( lexer opening -- obj )
    [
        lex-til-whitespace drop 2nip
        dup
    ] dip 1 cut-slice* backtick-literal make-delimited-literal ;


ERROR: backslash-expects-whitespace slice ;
: read-backslash ( lexer slice -- obj )
    over ?lexer-nth blank? [
        ! \ foo, M\ foo
        [ skip-blanks lex-til-whitespace drop 2nip dup ] dip 1 cut-slice* backslash-literal make-delimited-literal
    ] [
        ! M\N
        merge-lex-til-whitespace make-tag-literal
    ] if ;

! If the slice is 0 width, we stopped on whitespace.
! Advance the index and read again!
: read-token-or-whitespace ( lexer slice -- slice )
    [ [ 1 + ] change-n lex-factor ]
    [ nip make-tag-literal ] if-empty ;

ERROR: mismatched-terminator lexer slice ;
: read-terminator ( lexer slice -- slice/f )
    2dup [ dup peek-tag ] dip delimiters-match? [
        nip terminator-literal make-tag-class-literal
    ] [
        roll-back-lexer f
    ] if ;

: gt-terminator ( lexer slice -- slice/f )
    2dup peek-merge-til-whitespace
    top-level-greater-than? [
        2dup [ dup peek-tag ] dip delimiters-match? [
            nip terminator-literal make-tag-class-literal
        ] [
            roll-back-lexer f
        ] if
    ] [
        >>partial [ 1 + ] change-n lex-factor
    ] if ;

: ?blank? ( ch/f -- blank/f )
    { [ blank? ] [ f = ] } 1|| ;

PRIVATE<
! work on underlying, index is on the @
! @foo
: left-decorator? ( slice -- ? )
    {
        [ char-before-slice ?blank? ]
        [ next-char-from-slice ?blank? not ]
    } 1&& ;

! foo@
: right-decorator? ( slice -- ? )
    {
        [ prev-char-from-slice-end ?blank? not ]
        [ next-char-from-slice ?blank? ]
    } 1&& ;

PRIVATE>

: read-decorator ( lexer slice -- obj )
    nip
    {
        { [ dup left-decorator? ] [ t make-decorator-sentinel ] }
        ! { [ dup right-decorator? ] [
        !    dup length 1 > [
        !        [ -1 + ] 2dip
        !        -1 modify-to make-tag-literal
        !    ] [
        !        f make-decorator-sentinel
        !    ] if ] }
        [ make-tag-literal ]
    } cond ;

COMPILE<
: lexer-rules>delimiters ( seq -- string )
    [ delimiter>> ] "" map-as ;

: lexer-rules>assoc ( seq -- seq' )
    [ [ delimiter>> ] [ generator>> 1quotation ] bi ] { } map>assoc ;
COMPILE>

! 0 "HI: ;" slice-til-either -> 3 "HI: ;" "HI:" CHAR: \:
MACRO: rules>call-lexer ( seq -- quot: ( lexer string -- literal ) )
    [ lexer-rules>delimiters ]
    [
        lexer-rules>assoc
        { f [ nip f like dup [ make-tag-literal ] when ] } suffix
    ] bi
    '[ dup _ lex-til-either [ 2drop ] 2dip _ case ] ;

CONSTANT: factor-lexing-rules {
    T{ line-comment-lexer { generator read-exclamation } { delimiter char: \! } }
    T{ backtick-lexer { generator read-backtick } { delimiter char: \` } }
    T{ backslash-lexer { generator read-backslash } { delimiter char: \\ } }
    T{ dquote-lexer { generator read-string } { delimiter char: \" } { escape char: \\ } }
    T{ decorator-lexer { generator read-decorator } { delimiter char: \@ } }
    
    T{ colon-lexer { generator read-colon } { delimiter char: \: } }
    T{ less-than-lexer { generator read-less-than } { delimiter char: \< } }
    T{ matched-lexer { generator read-bracket } { delimiter char: \[ } }
    T{ matched-lexer { generator read-brace } { delimiter char: \{ } }
    T{ matched-lexer { generator read-paren } { delimiter char: \( } }
    
    T{ terminator-lexer { generator read-terminator } { delimiter char: \; } }
    T{ terminator-lexer { generator read-terminator } { delimiter char: \] } }
    T{ terminator-lexer { generator read-terminator } { delimiter char: \} } }
    T{ terminator-lexer { generator read-terminator } { delimiter char: \) } }
    T{ terminator-lexer { generator gt-terminator } { delimiter char: \> } }
    
    T{ whitespace-lexer { generator read-token-or-whitespace } { delimiter char: \s } }
    T{ whitespace-lexer { generator read-token-or-whitespace } { delimiter char: \r } }
    T{ whitespace-lexer { generator read-token-or-whitespace } { delimiter char: \n } }
} ;

: lex-factor ( lexer -- literal )
    factor-lexing-rules rules>call-lexer ;

: string>literals ( string -- sequence )
    <modern-lexer> '[ _ lex-factor ] loop>array postprocess-lexed ;

: path>literals ( path -- sequence )
    utf8 file-contents string>literals ;

: vocab>literals ( vocab -- sequence )
    ".private" ?tail drop
    vocab-source-path path>literals ;

! What a lexer body looks like, produced by make-lexer
! : lex ( n/f string -- n'/f string literal )
    ! "!`\\\"[{(\s\r\n" slice-til-either {
        ! { char: ! [ read-exclamation ] }
        ! { char: ` [ read-backtick ] }
        ! { char: \ [ read-backslash ] }
        ! { char: \" [ read-string ] }
        ! { char: \[ [ read-bracket ] }
        ! { char: \{ [ read-brace ] }
        ! { char: \( [ read-paren ] }
        ! { char: \s [ read-token-or-whitespace ] }
        ! { char: \r [ read-token-or-whitespace ] }
        ! { char: \n [ read-token-or-whitespace ] }
        ! { f [ f like dup [ make-tag-literal ] when ] }
    ! } case ; inline
