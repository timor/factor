! Copyright (C) 2016 Doug Coleman.
! See http://factorcode.org/license.txt for BSD license.
USING: accessors arrays assocs combinators.short-circuit kernel
modern modern.paths sequences sequences.extras ;
IN: modern.refactor

: parse-all-paths ( -- seq )
    all-paths [ path>literals ] map-zip ;

: USING:? ( obj -- ? )
    { [ uppercase-colon-literal? ] [ tag>> "USING" sequence= ] } 1&& ;

: USE:? ( obj -- ? )
    { [ uppercase-colon-literal? ] [ tag>> "USE" sequence= ] } 1&& ;

: any-use-form? ( obj -- ? )
    { [ USE:? ] [ USING:? ] } 1|| ;


: multiline-comment? ( obj -- ? )
    { [ double-matched-literal? ] [ tag>> "!" sequence= ] } 1&& ;

: any-comment? ( obj -- ? )
    { [ line-comment-literal? ] [ multiline-comment? ] } 1|| ;

: find-using ( name -- paths )
    parse-all-paths $[
        nip
        dup { [ USING:? ] [ USE:? ] } 1|| [
            payload>> [ _ sequence= ] any?
        ] [ drop f ] if
    ] assoc-filter ;

: find-using-lists ( -- paths )
    parse-all-paths $[
        [ { [ USING:? ] [ USE:? ] } 1|| ] filter
        [ payload>> [ tag>> ] map ] map concat
    ] assoc-map ;
