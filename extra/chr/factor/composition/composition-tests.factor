USING: accessors arrays chr.factor.composition kernel kernel.private lists
sequences slots.private tools.test ;
IN: chr.factor.composition.tests

: nop ( -- ) ;
GENERIC: mylastcdr ( list -- obj )
M: list mylastcdr
    ! cdr>> [ mylastcdr ] (call) ;
    nop cdr>> [ mylastcdr ] (call) ;
    ! cdr>> mylastcdr ;
M: +nil+ mylastcdr ;
! M: object mylastcdr ;
! M: array mylastcdr 2 slot [ mylastcdr ] (call) ;
: array-first ( arr -- thing ) 2 slot ;
M: array mylastcdr array-first [ [ mylastcdr ] (call) ] (call) ;
