USING: ;

IN: chr

! Constraint handling rules for Factor

! Design:
! - try to keep dsl-like to make compilation easier
! - meta-object-protocol to leave implementation extensible
! CHR constraints as procedure calls:
! each newly added constraint searches for possible matching rules in order, until
! all matching rules have been executed or the constraint is deleted from the store.

TUPLE: rule
    name
    head
    body ;

! adding rules
<PRIVATE
SYMBOL: rules

: make-rule ( name head body -- )

PRIVATE>

Defer: --
DEFER: |
SYNTAX: CHR: scan-token \ | parse-until \ ; parse-until make-rule ;

GENERIC: compile-rule
