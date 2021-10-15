USING: assocs kernel lists math math.parser namespaces sequences ;

IN: types.util

! * Helpers which should go to relevant vocabs

! TODO: move to lists vocab
: list*>array ( list -- array lastcdr )
    { } swap [ dup cons-state? ] [ uncons [ suffix ] dip ] while ;

! TODO: move to lists vocab
: sequence>list* ( sequence lastcdr -- list )
    [ <reversed> ] dip [ swons ] reduce ;

! TODO: move to list vocab
: lmap* ( list quot: ( car -- car' ) -- list )
    [ list*>array ] dip swap
    [ map ] dip sequence>list* ; inline

! Unicode stuff

CONSTANT: superscript-table H{
    { CHAR: 0 CHAR: ⁰ }
    { CHAR: 1 CHAR: ¹ }
    { CHAR: 2 CHAR: ² }
    { CHAR: 3 CHAR: ³ }
    { CHAR: 4 CHAR: ⁴ }
    { CHAR: 5 CHAR: ⁵ }
    { CHAR: 6 CHAR: ⁶ }
    { CHAR: 7 CHAR: ⁷ }
    { CHAR: 8 CHAR: ⁸ }
    { CHAR: 9 CHAR: ⁹ }
    { CHAR: - CHAR: ⁻ }
}

CONSTANT: subscript-table H{
    { CHAR: 0 CHAR: ₀ }
    { CHAR: 1 CHAR: ₁ }
    { CHAR: 2 CHAR: ₂ }
    { CHAR: 3 CHAR: ₃ }
    { CHAR: 4 CHAR: ₄ }
    { CHAR: 5 CHAR: ₆ }
    { CHAR: 6 CHAR: ₇ }
    { CHAR: 7 CHAR: ₈ }
    { CHAR: 8 CHAR: ₉ }
    { CHAR: 9 CHAR: ₉ }
    { CHAR: - CHAR: ₋ }
}

: lookup-chars ( assoc string -- string )
    [ ?at drop ] curry map ;

: number>superscript ( n -- string )
    number>string superscript-table lookup-chars ;

: number>subscript ( n -- string )
    number>string subscript-table lookup-chars ;

! Reverse if
: fi ( true false ? -- )
    -rot if ; inline

SYMBOL: debug-unify
: when-debug ( quot level -- )
    [ ] swap debug-unify get -1 or <= fi ; inline

: spprint ( obj -- str )
    [ pprint ] with-string-writer ;

ERROR: different-lengths seq1 seq2 ;
: assert-same-length ( seq1 seq2 -- seq1 seq2 )
    2dup [ length ] bi@ = not [ different-lengths ] when ;
