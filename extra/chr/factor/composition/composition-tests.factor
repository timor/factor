USING: accessors arrays chr.factor.composition kernel kernel.private lists
sequences slots.private tools.test ;
IN: chr.factor.composition.tests

: nop ( -- ) ;
GENERIC: mylastcdr ( list -- obj )
M: list mylastcdr

    ! RES3 needed for [ mylastcdr ]
    ! not working with [ [ mylastcdr ] ] (neither RES1,2,3 cause progress)
    ! RES2 needed for [ [ mylastcdr ] (call) ]
    cdr>> [ mylastcdr ] swap swap (call) ;

    ! HA! This works with RES2!
    ! cdr>> [ nop mylastcdr ] (call) ;

    ! nop cdr>> [ mylastcdr ] (call) ;

    ! cdr>> nop [ mylastcdr ] (call) ;


    ! cdr>> [ [ mylastcdr ] ] (call) (call) ; ! Doesnt work so well...

    ! RES3 needed for [ mylastcdr ]
    ! RES1 needed for [ [ mylastcdr ] ]
    ! RES3 needed for [ [ mylastcdr ] (call) ]
    ! RES2 needed for [ [ [ mylastcdr ] (call) ] (call) ]
    ! RES1 needed for [ [ [ mylastcdr ] ] (call) (call) ]
    ! cdr>> [ [ mylastcdr ] (call) ] (call) ; ! Works well

    ! RES2 needed for [ [ mylastcdr ] ]
    ! RES2 needed for [ [ mylastcdr ] (call) ]
    ! RES2 needed for [ [ [ mylastcdr ] (call) ] (call) ]
    ! RES2 needed for [ [ [ mylastcdr ] ] (call) (call) ]
    ! cdr>> mylastcdr ;
M: +nil+ mylastcdr ;
! M: object mylastcdr ;
! M: array mylastcdr 2 slot [ mylastcdr ] (call) ;
: array-first ( arr -- thing ) 2 slot ;
! M: array mylastcdr array-first [ [ mylastcdr ] (call) ] (call) ;
