USING: ;

IN: chr

! Constraint handling rules for Factor

! Design:
! - try to keep dsl-like to make compilation easier
! - meta-object-protocol to leave implementation extensible


! adding rules
<PRIVATE
SYMBOL: rules
PRIVATE>
