! Copyright (C) 2016 Doug Coleman.
! See http://factorcode.org/license.txt for BSD license.
USING: accessors combinators combinators.short-circuit
combinators.smart continuations fry io io.encodings.utf8
io.files io.streams.string kernel modern modern.paths
modern.slices multiline namespaces prettyprint sequences sets
splitting strings arrays unicode ;
IN: modern.out

symbol: last-slice

: replace-whitespace ( string -- string' )
    [ dup blank? [ drop char: \s ] unless ] map ;

: write-whitespace ( obj -- )
    ! [ last-slice get [ swap slice-between ] [ slice-before ] if* io:write ]
    [ last-slice get [ swap slice-between replace-whitespace io:write ] [ drop ] if* ]
    [ last-slice namespaces:set ] bi ;

defer: write-literal
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

M: uppercase-colon-literal write-literal
    {
        [ seq>> 0 swap nth write-whitespace ]
        [ tag>> write ]
        [ seq>> 1 swap nth write-whitespace ]
        [ delimiter>> write ]
        [ payload>> [ write-literal ] each ] ! don't need write-whitespace here, the recursion does it
        [ seq>> 3 swap nth [ lexed-underlying [ write-whitespace ] when* ] when* ]
        [ closing-tag>> [ write ] when* ]
    } cleave ;

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
            '[
                dup compound-sequence-literal? [ sequence>> ] when
                [ _ map-literals ] map
            ] change-payload
        ] 2bi
    ] [
        call
    ] if ; inline recursive

: rewrite-path ( path quot -- )
    ! dup print
    '[ [ path>literals [ _ map-literals ] map ] [ ] bi write-modern-path ]
    [ drop . ] recover ; inline

: rewrite-string ( string quot -- )
    ! dup print
    [ string>literals ] dip '[ _ map-literals ] map write-modern-string ; inline

: rewrite-paths ( seq quot -- ) '[ _ rewrite-path ] each ; inline
: lexable-core-paths ( -- seq ) core-source-paths ;
: lexable-basis-paths ( -- seq )
    basis-source-paths {
    } diff ;

: lexable-extra-paths ( -- seq )
    extra-source-paths {
    } diff ;

/*
! These work except they use pegs/ebnf, grep for [[ ]]
	modified:   basis/db/sqlite/errors/errors.factor
	modified:   basis/formatting/formatting.factor
	modified:   basis/globs/globs.factor
	modified:   extra/alien/fortran/fortran.factor
	modified:   extra/cpu/8080/emulator/emulator.factor
	modified:   extra/peg/expr/expr.factor
	modified:   extra/rosetta-code/arithmetic-evaluation/arithmetic-evaluation.factor
	modified:   extra/shell/parser/parser.factor
*/

: lexable-paths ( -- seq )
    [
        lexable-core-paths
        lexable-basis-paths
        lexable-extra-paths
    ] append-outputs ;

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
    lexable-paths swap rewrite-paths ; inline

: transform-core ( quot -- )
    lexable-core-paths swap rewrite-paths ; inline
