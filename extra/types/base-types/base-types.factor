USING: accessors arrays assocs assocs.extras combinators
combinators.short-circuit hashtables kernel math namespaces sequences sets
strings terms ;

IN: types.base-types

FROM: namespaces => set ;

! * Atomic type variables and Primitives
TUPLE: type-var
    { name string read-only }
    { id integer read-only }
    { order integer read-only } ;
GENERIC: change-type-var-order ( amount term -- term )
PREDICATE: base-type-var < type-var order>> 0 = ;
PREDICATE: dup-type-var < type-var order>> 0 > ;
! INSTANCE: base-type-var term-var
INSTANCE: type-var term-var
! INSTANCE: dup-type-var proper-term
! M: dup-type-var args>> drop f ;

: base-var= ( type-var1 type-var2 -- ? )
    { [ [ name>> ] bi@ = ]
      [ [ id>> ] bi@ = ]
    } 2&& ;

! Matches wrong order, need to correct replacement
M: type-var occurs-free?
    base-var= ;

: shift-term-non-recursive? ( replacement-term target-var eliminated-var -- ? )
    { [ drop swap occurs-free? not ]
    } 3&& ;

: shift-term-recursive? ( replacement-term target-var eliminated-var -- ? )
    { [ drop swap occurs-free? ]
      [ [ order>> ] bi@ >= nip ]
    } 3&& ;

SYMBOL: shifting?

GENERIC: shift-vars ( except amount term -- term )
M: type-var shift-vars
    rot dupd in?
    [ nip ] [ change-type-var-order ] if ;
M: proper-term shift-vars
    [ shift-vars ] 2with map-args ;

: shift-non-recursive ( amount replacement-term -- term )
    [ f ] 2dip shift-vars ;

! Two steps:
! 1. shift all vars except for the one we are replacing
! 2. substitute the old term into the var
: shift-step-recursive ( replacement-term var -- term )
    swap
    [ [ 1array 1 ] dip shift-vars ]
    [ shifting? [ subst-in-term ] with-variable-on ] 2bi ;

: shift-term-recursive ( replacement-term target-var eliminated-var -- term )
    [ [ order>> ] bi@ - ] keep swap
    [ shift-step-recursive ] with times ;

! FIXME: Can obviously directly count up
: shift-term-non-recursive ( replacement-term target-var eliminated-var -- term )
    [ order>> ] bi@ - swap shift-non-recursive ;

! Handling replacements
: lift-order-var ( target-term-var eliminated-type-var replacement-term -- term )
    -rot {
        { [ 2dup = ] [ 2drop ] } ! NOTE: redundant, same as shift=0 (except for recursion check!)
        { [ 3dup shift-term-recursive? ] [ shift-term-recursive ] }
        { [ 3dup shift-term-non-recursive? ] [ shift-term-non-recursive ] }
        [ 2drop ]
    } cond ;

: substitution-match? ( subst term -- term alist )
    swap over [ base-var= ] curry filter-keys
    dup assoc-size 1 > [ "huh?" throw ] when
    >alist ;

M: type-var lift* ( subst term -- term )
    substitution-match?
    [ first first2
      shifting? get
      [ 2nip ]
      [ lift-order-var ] if
    ] unless-empty
    ;




! Syntax type
TUPLE: dup-type element ;
C: <dup-type> dup-type
INSTANCE: dup-type proper-term
M: dup-type args>> element>> 1array ;
M: dup-type from-args* drop
    first <dup-type> ;
! M: dup-type lift*
!     element>> lift*
!     <dup-type> ;
! M: dup-type occurs-free? 2drop f ;

GENERIC: propagate-drop ( term -- term )
TUPLE: drop-type element ;
INSTANCE: drop-type proper-term
C: <drop-type> drop-type
M: drop-type args>> element>> 1array ;
M: drop-type from-args*
    drop first <drop-type> ;
! M: drop-type lift* nip ;
    ! element>> lift* propagate-drop ;


M: type-var change-type-var-order
    swap [ [ name>> ] [ id>> ] [ order>> ] tri ] dip
    + type-var boa ;

M: type-var propagate-drop
    <drop-type> ;

PREDICATE: dup-var < dup-type element>> type-var? ;
INSTANCE: dup-var term-var

: <type-var> ( name id -- obj )
    0 type-var boa ;

TUPLE: type-const thing ;
C: <type-const> type-const
INSTANCE: type-const proper-term
M: type-const args>> drop f ;
M: type-const change-type-var-order nip ;
M: type-const propagate-drop ;

TUPLE: rec-type { rec-var type-var } element ;
C: <rec-type> rec-type
INSTANCE: rec-type proper-term
! ! ERROR: rec-type-has-no-args rec-type ;
! M: rec-type args>> drop f ; ! rec-type-has-no-args ;
! M: rec-type occurs-free?
!     2dup rec-var>> =
!     [ 2drop f ]
!     [ element>> occurs-free? ] if ;
! ERROR: cannot-dup-recursive-type rec-type ;
! M: rec-type change-type-var-order cannot-dup-recursive-type ;
! ! Note: only free args!
! M: rec-type lift*
!     [ [ clone >hashtable ] dip
!       [ rec-var>> over delete-at ] [ element>> ] bi
!       lift* ]
!     [ rec-var>> ] bi swap <rec-type> ;

: should-lower-order? ( dropped-type-var type-var -- ? )
    { [ base-var= ]
      [ [ order>> ] bi@ < ]
    } 2&& ;

GENERIC: lower-var-orders ( type-var term -- term )
M: type-var lower-var-orders
    2dup should-lower-order?
    [ -1 swap change-type-var-order ] when
    nip ;
M: proper-term lower-var-orders
    [ lower-var-orders ] with map-args ;

GENERIC: change-term-var-orders ( amount type-var term -- term )
M: type-var change-term-var-orders
    2dup base-var=
    [ nip change-type-var-order ]
    [ 2nip ] if ;

M: proper-term change-term-var-orders
   [ change-term-var-orders ] 2with map-args ;
