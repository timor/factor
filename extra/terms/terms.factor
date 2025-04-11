USING: assocs kernel math mirrors sequences strings variants ;

IN: terms

! Disjoint set of variable equivalence sets
! TODO: make global for performance increase, in that case, move to
! terms.context vocabulary or some such
! TODO: find better name!
VAR: eqs


TUPLE: term-var
    { name string read-only }
    { counter fixnum read-only } ;

M: term-var equal?
    eqs equiv? ;

C: <term-var> term-var

GENERIC: fresh ( term -- term' )
M: term-var fresh
    ! TODO: check for overflow
    term-var unboa 1 + <term-var> ;

M: sequence fresh
    [ fresh ] map ;

M: tuple fresh
    clone dup <mirror> dup '[ drop _ [ fresh ] change-at ] assoc-each ;

M: object fresh ;
M: string fresh ;

GENERIC: subst ( subst term -- term' )
M: term-var subst
    swap ?at drop ;

M: sequence subst
    [ subst ] with map ;

M: tuple subst
    tuple>array unclip [ [ subst ] with map ] dip slots>tuple ;

M: object subst nip ;
M: string subst nip ;
