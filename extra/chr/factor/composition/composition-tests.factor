USING: tools.test chr.factor.composition ;
IN: chr.factor.composition.tests

GENERIC: mylastcdr ( list -- obj )
M: list mylastcdr
    cdr>> mylastcdr ;
M: +nil+ mylastcdr ;
! M: object mylastcdr ;
