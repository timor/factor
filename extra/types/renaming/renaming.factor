USING: accessors arrays ascii assocs classes.algebra combinators
combinators.short-circuit effects hash-sets kernel math math.parser namespaces
sequences sequences.extras sets strings words ;

IN: types.renaming

FROM: namespaces => set ;

! Helper lib for keeping track of unique names

TUPLE: varname
    { name maybe{ string } }
    { id integer } ;
C: <varname> varname
M: varname effect>string
    [ name>> ] [ id>> ] bi number>string append ;
TUPLE: rowvarname < varname ;
C: <rowvarname> rowvarname

GENERIC: next-var-name ( varname -- varname )
M: varname next-var-name
    [ name>> ] [ id>> 1 + ] bi <varname> ;
M: rowvarname next-var-name
    [ name>> ] [ id>> 1 + ] bi <rowvarname> ;

SYMBOL: name-counters

: with-name-counters ( quot -- )
    [ H{ } clone name-counters ] dip
    with-variable ; inline

: id-for ( key -- id/f )
    name-counters get at ;

: new-id-for ( key -- id )
    name-counters get [ 0 or 1 + dup ] change-at ;

SYMBOL: bound-names
SYMBOLS: mappings row-var-mappings ;

: ensure-unique-var ( varname -- varname )
    dup bound-names get in?
    [ next-var-name ensure-unique-var ]
    [ dup bound-names get adjoin ] if ;

! * Convert strings to variable names
: trim-varname ( str -- str n )
    [ digit? ] cut-when string>number 0 or ;

! Make sure we correctly re-label variable names
GENERIC: name>vars* ( effect -- effect )
PREDICATE: anon-effect < effect variable-effect? not ;

: make-anon-row-var ( -- rowvarname )
    "r" 0 <rowvarname> ensure-unique-var ;

M: anon-effect name>vars*
    [ make-anon-row-var dup ] dip
    [ in>> ] [ out>> ] bi [ [ name>vars* ] map ] bi@
    swapd <variable-effect> ;

: map-rowvarname ( str -- varname )
    row-var-mappings get [ trim-varname <rowvarname> ensure-unique-var ] cache ;

M: effect name>vars*
    {
        [ in-var>> map-rowvarname ]
        [ in>> [ name>vars* ] map ]
        [ out-var>> map-rowvarname ]
        [ out>> [ name>vars* ] map ]
    } cleave
    <variable-effect> ;

: map-varname ( str -- varname )
    mappings get [ trim-varname <varname> ensure-unique-var ] cache ;

M: string name>vars*
    map-varname ;
M: word name>vars* ;
M: pair name>vars*
    [ first name>vars* ]
    [ second name>vars* ] bi 2array ;

: name>vars ( effect -- effect )
    [ HS{ } clone bound-names set
      H{ } clone mappings set
      H{ } clone row-var-mappings set
      name>vars*
    ] with-name-counters ;

SYMBOL: renamings
GENERIC: rename-vars* ( effect -- effect )
M: word rename-vars* ;
M: varname rename-vars*
    renamings get [ ensure-unique-var ] cache ;
M: sequence rename-vars*
    [ rename-vars* ] map ;
M: effect rename-vars*
    {
        [ in-var>> rename-vars* ]
        [ in>> rename-vars* ]
        [ out-var>> rename-vars* ]
        [ out>> rename-vars* ]
    } cleave <variable-effect> ;

: rename-vars ( bound effect -- bound' effect' )
    [ swap HS{ } clone or bound-names set
      H{ } clone renamings set
      rename-vars*
      bound-names get renamings get keys >hash-set union swap
    ] with-scope ;

: rename-effects ( effect1 effect2 -- var-effect1 var-effect2 )
    [ name>vars ] bi@
    [ f swap rename-vars swap ]
    [ rename-vars ] bi* nip ;
