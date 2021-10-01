USING: kernel lists sequences ;

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
