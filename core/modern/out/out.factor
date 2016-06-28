! Copyright (C) 2016 Doug Coleman.
! See http://factorcode.org/license.txt for BSD license.
USING: accessors arrays assocs combinators
combinators.short-circuit combinators.smart continuations fry io
io.encodings.utf8 io.files io.streams.string kernel math modern
modern.paths modern.refactor modern.slices namespaces
prettyprint sequences sequences.extras sets splitting
splitting.monotonic strings unicode ;
IN: modern.out

SYMBOL: last-slice

: replace-whitespace ( string -- string' )
    dup [ "\r\n" member? ] find drop [ tail ] when*
    [ dup blank? [ drop char: \s ] unless ] map ;

: write-whitespace ( obj -- )
    [ last-slice get [ swap slice-between ] [ slice-before ] if* replace-whitespace io:write ]
    [ last-slice namespaces:set ] bi ;

: write-whitespace-nice ( obj tag -- )
    [
        [ last-slice get [ swap slice-between ] [ slice-before ] if* replace-whitespace ] dip
        length modify-from io:write
    ] [ drop last-slice namespaces:set ] 2bi ;

CONSTANT: janky-arities H{
    `DEFER 1 --
    `FORGET 1 --
    `IN 1 --
    `USE 1 --
    `UNUSE 1 --
    `SYMBOL 1 --
    `SINGLETON 1 --
    `B 1 --
    `MAIN 1 --
    `LEFT-DECORATOR 1 --
    `ABOUT 1 --
    `SOLUTION 1 --
    `OPCODE 1 --
    `CYCLES 1 --
    `MIXIN 1 --
    `SLOT 1 --
    `SLOT-CONSTRUCTOR 1 --
    `MAIN 1 --
    `SPECIALIZED-ARRAY 1 --
    `SPECIALIZED-VECTOR 1 --
    `8-BIT 1 --
    `TUPLE-ARRAY 1 --
    `C-TYPE 1 --
    `LIBRARY 1 --
    `DESTRUCTOR 1 --
    `COMPONENT 1 --
    `FRAMEWORK 1 --
    `REGISTER 1 --
    `FORWARD-ANALYSIS 1 --
    `BACKWARD-ANALYSIS 1 --
    `VECTORED-STRUCT 1 --
    `IMPORT 1 --
    `GIR 1 --
    `PIXEL-FORMAT-ATTRIBUTE-TABLE 1 --
    `TEST 1 --
    `SELECTOR 1 --
    `SIMD-128 1 --

    `ALIAS 2 --
    `ARITY 2 --
    `C 2 --
    `CONSTANT 2 --
    `INSTANCE 2 --
    `GENERIC 2 --
    `PRIMITIVE 2 --
    `QUALIFIED 2 --

    `GENERIC# 3 --
    `HOOK 3
} ;

GENERIC: write-literal ( obj -- ) ;
! M: object write-literal lexed-underlying write ;
M: string write-literal write ;
M: slice write-literal [ write-whitespace ] [ write ] bi ;

M: array write-literal [ write-literal ] each ;

M: tag-literal write-literal
    {
        [ seq>> 0 swap nth write-whitespace ]
        [ tag>> write ]
    } cleave ;

: split-last ( seq quot -- head tail )
    [ count-tail ] 2keep drop swap cut* ; inline

M: single-matched-literal write-literal
    {
        [ seq>> 0 swap nth write-whitespace ]
        [ tag>> write ]
        [ seq>> 1 swap nth write-whitespace ]
        [ delimiter>> write ]
        [ payload>> write-literal ] ! don't need write-whitespace here, the recursion does it
        [ seq>> 3 swap nth lexed-underlying [ write-whitespace ] when* ]
        [ closing-tag>> [ write ] when* ]
    } cleave ;

M: double-matched-literal write-literal
    {
        [ seq>> 0 swap nth write-whitespace ]
        [ tag>> io:write ]
        [ seq>> 1 swap nth write-whitespace ]
        [ delimiter>> io:write ]
        [ seq>> 2 swap nth write-whitespace ]
        [ payload>> io:write ]
        [ seq>> 3 swap nth write-whitespace ]
        [ delimiter>> matching-delimiter-string io:write ]
    } cleave ;

M: dquote-literal write-literal
    {
        [ seq>> 0 swap nth write-whitespace ]
        [ tag>> io:write ]
        [ seq>> 1 swap nth write-whitespace ]
        [ delimiter>> io:write ]
        [ seq>> 2 swap nth write-whitespace ]
        [ payload>> io:write ]
        [ seq>> 3 swap nth write-whitespace ]
        [ delimiter>> matching-delimiter-string io:write ]
    } cleave ;

M: backtick-literal write-literal
    {
        [ seq>> 0 swap nth write-whitespace ]
        [ tag>> io:write ]
        [ seq>> 1 swap nth write-whitespace ]
        [ delimiter>> io:write ]
        [ seq>> 2 swap nth write-whitespace ]
        [ payload>> io:write ]
    } cleave ;

M: backslash-literal write-literal
    {
        [ seq>> 0 swap nth write-whitespace ]
        [ tag>> io:write ]
        [ seq>> 1 swap nth write-whitespace ]
        [ delimiter>> io:write ]
        [ seq>> 2 swap nth write-whitespace ]
        [ payload>> io:write ]
    } cleave ;

M: line-comment-literal write-literal
    {
        [ seq>> 0 swap nth write-whitespace ]
        [ tag>> io:write ]
        [ seq>> 1 swap nth write-whitespace ]
        [ delimiter>> io:write ]
        [ seq>> 2 swap nth write-whitespace ]
        [ payload>> io:write ]
    } cleave ;


: adding-semi? ( obj -- ? )
    { [ seq>> 3 swap ?nth not ] [ closing-tag>> ] } 1&& ;

: removing-semi? ( obj -- ? )
    { [ seq>> 3 swap ?nth ] [ closing-tag>> not ] } 1&& ;

: changing-semi? ( obj -- ? )
    { [ adding-semi? ] [ removing-semi? ] } 1|| ;

! either adding or removing a semi
: write-uppercase-colon-literal-nice ( obj -- )
    {
        [ seq>> 0 swap nth write-whitespace ]
        [ tag>> write ]
        [ seq>> 1 swap nth write-whitespace ]
        [ delimiter>> write ]
        [
            dup payload>> [ line-comment-literal? ] split-last
            [ drop nip write-literal ]
            [ 2drop closing-tag>> [ write ] when* ]
            [ 2nip write-literal ] 3tri
        ]
        [
            seq>> 3 swap ?nth
            [ tag>> length 1 + last-slice swap $[ _ modify-to ] change ] when*
        ]
    } cleave ;

: write-uppercase-colon-literal-vanilla ( obj -- )
    {
        [ seq>> 0 swap nth write-whitespace ]
        [ tag>> write ]
        [ seq>> 1 swap nth write-whitespace ]
        [ delimiter>> write ]
        [ payload>> [ write-literal ] each ] ! don't need write-whitespace here, the recursion does it
        [
            seq>> 3 swap ?nth
            [ lexed-underlying [ write-whitespace ] when* ] when*
        ]
        [ closing-tag>> [ write ] when* ]
    } cleave ;

M: uppercase-colon-literal write-literal
    dup changing-semi? [
        write-uppercase-colon-literal-nice
    ] [
        write-uppercase-colon-literal-vanilla
    ] if ;


M: lowercase-colon-literal write-literal
    {
        [ seq>> 0 swap nth write-whitespace ]
        [ tag>> io:write ]
        [ seq>> 1 swap nth write-whitespace ]
        [ delimiter>> io:write ]
        [ payload>> write-literal ] ! don't need write-whitespace here, the recursion does it
    } cleave ;

M: left-decorator-literal write-literal
    {
        [ seq>> 0 swap nth write-whitespace ]
        [ delimiter>> io:write ]
        [ payload>> write-literal ] ! don't need write-whitespace here, the recursion does it
    } cleave ;

M: right-decorator-literal write-literal
    {
        [ payload>> write-literal ] ! don't need write-whitespace here, the recursion does it
        [ seq>> 0 swap nth write-whitespace ]
        [ delimiter>> io:write ]
    } cleave ;

M: compound-literal write-literal
    sequence>> [ write-literal ] each ;

M: compound-sequence-literal write-literal
    sequence>> [ write-literal ] each ;

! Swap in write-literal for renaming

: write-modern-loop ( quot -- )
    [ write-literal ] each ; inline

: write-modern-string ( seq -- string )
    [ write-modern-loop ] with-string-writer ; inline

: write-modern-path ( seq path -- )
    utf8 [ write-modern-loop nl ] with-file-writer ; inline

: map-literals ( obj quot: ( obj -- obj' ) -- seq )
    over single-matched-literal? [
        [ call drop ] [
            $[
                dup compound-sequence-literal? [ sequence>> ] when
                [ _ map-literals ] map
            ] change-payload
        ] 2bi
    ] [
        call
    ] if ; inline recursive


GENERIC: fixup-arity ( obj -- seq ) ;

ERROR: closing-tag-required2 obj ;
M: uppercase-colon-literal fixup-arity
    dup tag>> janky-arities ?at [
        $[ _ swap [ any-comment? not ] cut-nth-match swap ] change-payload
        swap 2array
        ! dup first f >>closing-tag drop
        ! dup first " ;" >>closing-tag drop
    ] [
        drop
        dup closing-tag>> [ B closing-tag-required2 ] unless
    ] if ;

M: less-than-literal fixup-arity
    [ [ fixup-arity ] map ] change-payload ;

M: object fixup-arity ;

: rewrite-path ( path quot -- )
    ! dup print
    $[
        [
            path>literals
            [ _ map-literals ] map
            [ fixup-arity ] map
        ] [ ] bi write-modern-path ]
    [ drop . ] recover ; inline

: rewrite-string ( string quot -- )
    ! dup print
    [ string>literals ] dip $[ _ map-literals ] map
    ! colons
    [ fixup-arity ] map
    write-modern-string ; inline

: rewrite-paths ( seq quot -- ) $[ _ rewrite-path ] each ; inline


: paren-word>tick-word ( string -- string' )
    dup [ "(" ?head drop ")" ?tail drop "'" append ] [ ] if ;

: paren-word-name? ( string -- ? )
    { [ "(" head? ] [ ")" tail? ] } 1&& ;

: transform-paren-word>tick-word ( token -- token' )
    dup { [ tag-literal? ] [ tag>> paren-word-name? ] } 1&& [
        [ paren-word>tick-word ] change-tag
    ] when ;

: single-line-comment? ( token -- ? )
    { [ line-comment-literal? ] [ delimiter>> "!" sequence= ] } 1&& ;

: transform-single-line-comment>hash-comment ( token -- token' )
    dup single-line-comment? [
        [ drop "#" ] change-delimiter
    ] when ;

: transform-source ( quot -- )
    all-paths swap rewrite-paths ; inline
