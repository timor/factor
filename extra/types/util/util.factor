USING: assocs kernel lists math.parser sequences ;

IN: types.util

! * Helpers which should go to relevant vocabs

! TODO: move to lists vocab
: list*>array ( list -- array lastcdr )
    { } swap [ dup list? ] [ uncons [ suffix ] dip ] while ;

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

: number>superscript ( n -- string )
    number>string
    superscript-table [ ?at drop ] curry map ;
