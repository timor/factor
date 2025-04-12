USING: assocs classes.tuple disjoint-sets kernel math mirrors sequences strings
terms.context variants ;

IN: terms

TUPLE: term-var
    { name string read-only } ;

M: term-var equal?
    over term-var?
    [ equivs equiv? ]
    [ 2drop f ] if ; inline

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
