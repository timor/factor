USING: accessors assocs classes.tuple colors disjoint-sets hashtables io.styles
kernel math math.parser mirrors prettyprint.custom prettyprint.sections
sequences strings terms.context terms.util variables words ;

IN: terms


! Term variables

! TUPLE: term-var
!     { name string read-only } ;

! Used to distinguish between variables with different identities in print
<PRIVATE
TYPED-VAR: index-counter hashtable
TYPED-VAR: var-index hashtable

: get-var-index ( var -- index )
    var-index
    [ name>> index-counter [ 1 ] 2dip [ 0 or + dup ] change-at ]
    cache ;

PRIVATE>

PREDICATE: term-var < word "term-var" word-prop ;
M: term-var reset-word
    [ call-next-method ]
    [ f "term-var" set-word-prop ] bi ;

: <term-var> ( name -- var )
    <uninterned-word>
    dup t "term-var" set-word-prop ;

M: term-var equal?
    over term-var?
    [ equivs [ equiv? ] [ 2drop f ] if* ]
    [ 2drop f ] if ; inline

M: term-var clone
    name>> <term-var> ;

! TODO: that will probably have to be fresh-with, keeping track of which vars to
! alpha-rename somewhere above
GENERIC: fresh ( term -- term' )
M: term-var fresh
    clone ;

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
    [ name>> ]
    [ get-var-index number>string >subscript ] bi append
    H{ { foreground COLOR: solarized-blue } } styled-text ;
