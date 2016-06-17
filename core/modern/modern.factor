! Copyright (C) 2016 Doug Coleman.
! See http://factorcode.org/license.txt for BSD license.
USING: accessors arrays assocs assocs.extras combinators
combinators.short-circuit constructors continuations fry
io.encodings.utf8 io.files kernel locals macros make math
math.order modern.paths modern.slices multiline namespaces
quotations sequences sequences.extras splitting
splitting.monotonic strings unicode generalizations ;
in: modern

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

TUPLE: dquote-literal < delimited-literal ;
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
    dup [ { [ tag-literal? ] [ tag>> "--" = ] } 1&& ] split-when
    dup length 1 > [
        nip <compound-sequence-literal>
    ] [
        drop
    ] if ;

: postprocess-lexed ( seq -- seq' )
    collapse-decorators make-compound-literals ;


: strict-upper? ( string -- ? )
    [ { [ char: A char: Z between? ] [ char: 0 char: 9 between? ] [ "#:-<" member? ] } 1|| ] all? ;

: whitespace/f? ( ch -- ? )
    { char: \s char: \r char: \n f } member? ; inline

: scoped-colon-name ( string -- string' )
    dup [ length 2 - ] keep [ char: \: = ] find-last-from [ 1 + tail ] [ drop ] if ;

: scoped-less-than-name ( string -- string' )
    dup [ length 2 - ] keep [ char: < = ] find-last-from [ 1 + tail ] [ drop ] if ;

: scoped-upper? ( string -- ? )
    dup { [ ":" tail? ] [ "<" tail? ] } 1|| [
        dup length 1 > [
            [ [ ":<" member? ] trim-tail [ char: \: = ] find-last ] keep
            swap [ swap tail strict-upper? ] [ nip strict-upper? ] if
        ] [
            "<" sequence= not
        ] if
    ] [
        drop f
    ] if ;

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

ERROR: mismatched-closing opening closing ;
:: make-matched-literal ( payload closing tag opening-delimiter class -- literal )
    class new
        tag >string >>tag
        payload postprocess-lexed opening-delimiter "\"" = [ split-double-dash ] unless >>payload
        tag closing [ dup tag-literal? [ lexed-underlying ] when ] bi@ ?span-slices >>underlying
        opening-delimiter >string >>delimiter
        dup single-matched-literal? [
            closing dup [ tag>> ] when length 1 > [
                tag opening-delimiter append
                matching-delimiter-string closing dup [ tag>> ] when sequence=
                [ opening-delimiter closing tag>> mismatched-closing ] unless
            ] when
            closing dup [ tag>> ] when >>closing-tag
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

ERROR: long-opening-mismatch tag open n string ch ;

! (( )) [[ ]] {{ }}
MACRO:: read-double-matched ( open-ch -- quot: ( n string tag ch -- n' string seq ) )
    open-ch dup matching-delimiter {
        [ drop 2 swap <string> ]
        [ drop 1string ]
        [ nip 2 swap <string> ]
    } 2cleave :> ( openstr2 openstr1 closestr2 )
    |[ n string tag! ch |
        ch {
            { char: = [
                n string openstr1 slice-til-separator-inclusive [ -1 modify-from ] dip :> ( n' string' opening ch )
                ch open-ch = [ tag openstr2 n string ch long-opening-mismatch ] unless
                opening matching-delimiter-string :> needle

                n' string' needle slice-til-string :> ( n'' string'' payload closing )
                n'' string
                payload closing tag opening double-matched-literal make-matched-literal
            ] }
            { open-ch [
                tag 1 cut-slice* swap tag! 1 modify-to :> opening
                n 1 + string closestr2 slice-til-string :> ( n' string' payload closing )
                n' string
                payload closing tag opening double-matched-literal make-matched-literal
            ] }
            [ [ tag openstr2 n string ] dip long-opening-mismatch ]
        } case
     ] ;

: read-double-matched-paren ( n string tag ch -- n' string seq ) char: \( read-double-matched ;
: read-double-matched-bracket ( n string tag ch -- n' string seq ) char: \[ read-double-matched ;
: read-double-matched-brace ( n string tag ch -- n' string seq ) char: \{ read-double-matched ;

defer: lex
defer: lex-factor

! make lex-top-level and lex-matched
! lex-top-level lexes til FOO; ; or TAG:, on TAG: leave n' at start of TAG:
! lex-matched lexes til foo) foo} foo] ) } ] or TAG:, on TAG: throw error


ERROR: lex-expected-but-got-eof n string quot ;

ERROR: unnestable-form n string obj ;
! For implementing [ { (
: lex-until ( nested n string tags -- nested' n' string payload closing )
    ! 3 npick [ lex-expected-but-got-eof ] unless
    '[
        [
            lex-factor [
                ! [ _ _ _ lex-expected-but-got-eof ] unless*
                dup tag-literal? [
                    dup ,
                    underlying>> ! { [ dup scoped-upper? ] [ 4 npick 0 > ] } 0&& [ unnestable-form ] when
                    _ [ sequence= ] with any? not
                ] [ , t ] if
            ] [
                f , f
            ] if*
        ] loop
    ] { } make unclip-last ; inline

MACRO:: read-matched ( ch -- quot: ( nested n string tag -- nested' n' string slice' ) )
    ch dup matching-delimiter {
        [ drop "=" swap prefix ]
        [ nip 1string ]
    } 2cleave :> ( openstreq closestr1 )  ! [= ]
    |[ nested n string tag |
        nested 1 + n string tag
        2over nth-check-eof {
            { [ dup openstreq member? ] [ ch read-double-matched ] } ! (=( or ((
            { [ dup blank? ] [ drop dup '[ _ matching-delimiter-string closestr1 2array lex-until ] dip 1 cut-slice* single-matched-literal make-matched-literal [ 1 - ] 3dip ] } ! ( foo )
            [ drop [ slice-til-whitespace drop ] dip span-slices make-tag-literal ]  ! (foo)
        } cond
    ] ;

: read-bracket ( nested n string slice -- nested' n' string slice' ) char: \[ read-matched ;
: read-brace ( nested n string slice -- nested' n' string slice' ) char: \{ read-matched ;
: read-paren ( nested n string slice -- nested' n' string slice' ) char: \( read-matched ;

: read-string-payload ( n string -- n' string )
    over [
        { char: \\ char: \" } slice-til-separator-inclusive {
            { f [ drop ] }
            { char: \" [ drop ] }
            { char: \\ [ drop next-char-from drop read-string-payload ] }
        } case
    ] [
        string-expected-got-eof
    ] if ;

:: read-string ( n string tag -- n' string seq )
    n string read-string-payload drop :> n'
    n' string
    n' [ n string string-expected-got-eof ] unless
    n n' 1 - string <slice>
    n' 1 - n' string <slice>
    tag 1 cut-slice* dquote-literal make-matched-literal ;



ERROR: cannot-nest-upper-colon nested n string string' ;
: read-upper-colon ( nested n string string' -- nested' n' string obj )
    4 npick 0 > [ cannot-nest-upper-colon ] when
    dup [ scoped-colon-name [ but-last ";" append ";" 2array ] [ ";" 1array ] if* lex-until ] dip
    1 cut-slice* uppercase-colon-literal make-matched-literal ;

: read-lower-colon ( nested' n string string' -- nested' n' string obj )
    [ lex-factor dup ] dip 1 cut-slice*
    lowercase-colon-literal make-delimited-literal ;

! : foo: :foo foo:bar foo:BAR: foo:bar: :foo:
: read-colon ( nested n string slice -- nested' n' string colon )
    merge-slice-til-whitespace {
        { [ dup length 1 = ] [ read-upper-colon ] }
        { [ dup [ char: \: = ] all? ] [ read-upper-colon ] }
        { [ dup { [ ":" head? ] [ ":" tail? ] } 1&& ] [ make-tag-literal ] }
        { [ dup ":" tail? ] [ dup scoped-upper? [ read-upper-colon ] [ read-lower-colon ] if ] }
        { [ dup ":" head? ] [ make-tag-literal ] } ! :foo( ... )
        [ make-tag-literal ]
    } cond ;



: read-upper-less-than ( nested n string slice -- nested' n' string less-than )
    dup [ scoped-less-than-name [ but-last ">" append 1array ] [ ">" 1array ] if* lex-until ] dip
    1 cut-slice* less-than-literal make-matched-literal ;

: read-less-than ( nested n string slice -- nested' n' string less-than )
    merge-slice-til-whitespace {
        { [ dup length 1 = ] [ make-tag-literal ] } ! "<"
        { [ dup "<" tail? ] [ dup scoped-upper? [ read-upper-less-than ] [ make-tag-literal ] if ] } ! FOO< or foo<
        [ make-tag-literal ]
    } cond ;


: take-comment ( n string slice -- n' string comment )
    2over ?nth char: \[ = [
        [ 1 + ] 2dip 2over ?nth read-double-matched-bracket
    ] [
        [ slice-til-eol drop dup ] dip 1 cut-slice* line-comment-literal make-delimited-literal
    ] if ;

! Words like append! and suffix! are allowed for now.
: read-exclamation ( n string slice -- n' string obj )
    dup { [ "!" sequence= ] [ "#!" sequence= ] } 1||
    [ take-comment ] [ merge-slice-til-whitespace make-tag-literal ] if ;


: read-backtick ( n string opening -- n' string obj )
    [
        slice-til-whitespace drop
        dup
    ] dip 1 cut-slice* backtick-literal make-delimited-literal ;


ERROR: backslash-expects-whitespace slice ;
: read-backslash ( n string slice -- n' string obj )
    2over peek-from blank? [
        ! \ foo, M\ foo
        [ skip-blank-from slice-til-whitespace drop dup ] dip 1 cut-slice* backslash-literal make-delimited-literal
    ] [
        ! M\N
        merge-slice-til-whitespace make-tag-literal
    ] if ;

! If the slice is 0 width, we stopped on whitespace.
! Advance the index and read again!
: read-token-or-whitespace ( nested n string slice -- nested' n' string slice )
    [ [ 1 + ] dip lex-factor ]
    [ make-tag-literal ] if-empty ;

ERROR: mismatched-terminator n string slice ;
: read-terminator ( n string slice -- n' string slice )
    terminator-literal make-tag-class-literal ;

: ?blank? ( ch/f -- blank/f )
    { [ blank? ] [ f = ] } 1|| ;

PRIVATE<
! work on underlying, index is on the @
! @foo
: left-decorator? ( obj -- ? )
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

: read-decorator ( n string slice -- n' string obj )
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
MACRO: rules>call-lexer ( seq -- quot: ( nested n/f string -- nested' n'/f string literal ) )
    [ lexer-rules>delimiters ]
    [
        lexer-rules>assoc
        { f [ f like dup [ make-tag-literal ] when ] } suffix
    ] bi
    '[ _ slice-til-either _ case ] ;

CONSTANT: factor-lexing-rules {
    T{ line-comment-lexer { generator read-exclamation } { delimiter char: \! } }
    T{ backtick-lexer { generator read-backtick } { delimiter char: ` } }
    T{ backslash-lexer { generator read-backslash } { delimiter char: \\ } }
    T{ dquote-lexer { generator read-string } { delimiter char: \" } { escape char: \\ } }
    T{ decorator-lexer { generator read-decorator } { delimiter char: @ } }
    
    T{ colon-lexer { generator read-colon } { delimiter char: \: } }
    T{ less-than-lexer { generator read-less-than } { delimiter char: < } }
    T{ matched-lexer { generator read-bracket } { delimiter char: \[ } }
    T{ matched-lexer { generator read-brace } { delimiter char: \{ } }
    T{ matched-lexer { generator read-paren } { delimiter char: \( } }
    
    T{ terminator-lexer { generator read-terminator } { delimiter char: ; } }
    T{ terminator-lexer { generator read-terminator } { delimiter char: ] } }
    T{ terminator-lexer { generator read-terminator } { delimiter char: } } }
    T{ terminator-lexer { generator read-terminator } { delimiter char: ) } }
    
    T{ whitespace-lexer { generator read-token-or-whitespace } { delimiter char: \s } }
    T{ whitespace-lexer { generator read-token-or-whitespace } { delimiter char: \r } }
    T{ whitespace-lexer { generator read-token-or-whitespace } { delimiter char: \n } }
} ;

: lex-factor ( nested n/f string -- nested' n'/f string literal )
    factor-lexing-rules rules>call-lexer ;

: string>literals ( string -- sequence )
    [ 0 0 ] dip [ lex-factor ] loop>array nip 2nip postprocess-lexed ;

: path>literals ( path -- sequence )
    utf8 file-contents string>literals ;

: vocab>literals ( vocab -- sequence )
    ".private" ?tail drop
    modern-source-path path>literals ;


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
