USING: accessors arrays ascii assocs hash-sets kernel math math.parser
namespaces sequences.extras sets terms types.base-types ;

IN: types.renaming

FROM: namespaces => set ;

! Helper lib for keeping track of unique names

! TODO split of the structure definitions into type language vocab

SYMBOL: name-counters

: with-name-counters ( quot -- )
    [ H{ } clone name-counters ] dip
    with-variable ; inline

: id-for ( key -- id/f )
    name-counters get at ;

: new-id-for ( key -- id )
    name-counters get [ 0 or 1 + dup ] change-at ;

! ! * Convert strings to variable names

! GENERIC: name>vars* ( effect -- effect )
! PREDICATE: anon-effect < effect variable-effect? not ;

! : make-anon-row-var ( -- rowvarname )
!     "S" 0 <type-var> ensure-unique-var ;

! M: anon-effect name>vars*
!     [ make-anon-row-var dup ] dip
!     [ in>> ] [ out>> ] bi [ [ name>vars* ] map ] bi@
!     swapd <variable-effect> ;

! GENERIC: map-rowvarname ( element -- varname )

! M: string map-rowvarname
!     row-var-mappings get [ trim-varname <rowvarname> ensure-unique-var ] cache ;
! M: dup-type map-rowvarname
!     element>> map-rowvarname <dup-type> ;
! : name>row-var ( string -- type-var )
!     capitalize name>vars* ;

! M: effect name>vars*
!     {
!         [ in-var>> name>row-var ]
!         [ in>> [ name>vars* ] map ]
!         [ out-var>> name>row-var ]
!         [ out>> [ name>vars* ] map ]
!     } cleave
!     <variable-effect> ;

! M: string name>vars*
!     map-varname ;
! M: word name>vars* ;
! M: pair name>vars*
!     [ first name>vars* ]
!     [ second name>vars* ] bi 2array ;
! M: dup-type name>vars*
!     element>> name>vars* <dup-type> ;
! M: rec-type name>vars*
!     [ rec-var>> name>vars* ] [ element>> name>vars* ] bi
!     <rec-type> ;

! : name>vars ( effect -- effect )
!     [ HS{ } clone bound-names set
!       H{ } clone mappings set
!       H{ } clone row-var-mappings set
!       name>vars*
!     ] with-name-counters ;

SYMBOL: bound-names
SYMBOLS: mappings ;

GENERIC: next-var-name ( varname -- varname )
M: type-var next-var-name
    [ name>> ] [ id>> 1 + ] [ order>> ] tri type-var boa ;

: type-var-key ( type-var -- key )
    [ name>> ] [ id>> ] bi 0 type-var boa ;

: ensure-unique-var ( varname -- varname )
    dup bound-names get in?
    [ next-var-name ensure-unique-var ]
    [ dup bound-names get adjoin ] if ;

: trim-varname ( str -- str n )
    [ digit? ] cut-when string>number 0 or ;

: map-varname ( str -- varname )
    mappings get [ trim-varname <type-var> ensure-unique-var ] cache ;

: with-unique-names ( quot -- )
    [
        HS{ } clone bound-names set
        H{ } clone mappings set
        call
    ] with-scope ; inline

SYMBOL: renamings
GENERIC: rename-vars* ( term -- term )
: ensure-unique-type-var ( type-var -- type-var )
    dup type-var-key bound-names get in?
    [ next-var-name rename-vars* ]
    [ dup type-var-key bound-names get adjoin ] if
    ;

M: type-const rename-vars* ;
M: type-var rename-vars*
    [ type-var-key renamings get [ ensure-unique-var ] cache
      [ name>> ] [ id>> ] bi
    ]
    [ order>> ] bi type-var boa
    ;
! M: dup-type-var rename-vars*
!     renamings get [ ensure-unique-var ] cache ;
M: proper-term rename-vars*
    [ rename-vars* ] map-args ;

! M: word rename-vars* ;
! M: varname rename-vars*
! M: dup-type rename-vars*
!     element>> rename-vars* <dup-type> ;
M: rec-type rename-vars*
    [ rec-var>> rename-vars* ] [ element>> rename-vars* ] bi
    <rec-type> ;
! M: sequence rename-vars*
!     [ rename-vars* ] map ;
! M: effect rename-vars*
!     {
!         [ in-var>> rename-vars* ]
!         [ in>> rename-vars* ]
!         [ out-var>> rename-vars* ]
!         [ out>> rename-vars* ]
!     } cleave <variable-effect> ;

: rename-vars ( bound term -- bound' term' )
    [ swap HS{ } clone or bound-names set
      H{ } clone renamings set
      rename-vars*
      bound-names get renamings get keys >hash-set union swap
    ] with-unique-names ;

: rename-2-terms ( term1 term2 -- term1 term2' )
    [ f swap rename-vars swap ]
    [ rename-vars ] bi* nip ;
