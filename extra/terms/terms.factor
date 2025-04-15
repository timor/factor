USING: accessors assocs classes.tuple colors disjoint-sets io.styles kernel
mirrors prettyprint.custom prettyprint.sections sequences strings terms.context
words ;

IN: terms


! Term variables

! TUPLE: term-var
!     { name string read-only } ;

PREDICATE: term-var < word "term-var" word-prop ;
M: term-var reset-word
    [ call-next-method ]
    [ f "term-var" set-word-prop ] bi ;

: <term-var> ( name -- var )
    <uninterned-word>
    dup t "term-var" set-word-prop ;
    ! defined-equalities
    ! [ dupd add-atom ] when* ;

M: term-var equal?
    over term-var?
    [ equivs [ equiv? ] [ 2drop f ] if* ]
    [ 2drop f ] if ; inline

GENERIC: fresh ( term -- term' )
M: term-var fresh
    name>> <term-var> ;

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

M: term-var pprint*
    name>> H{ { foreground COLOR: solarized-blue } } styled-text ;
