USING: accessors arrays assocs kernel math sequences strings terms ;

IN: types.base-types

FROM: namespaces => set ;

! * Atomic type variables and Primitives
TUPLE: type-var
    { name string read-only }
    { id integer read-only }
    { order integer read-only } ;
PREDICATE: base-type-var < type-var order>> 0 = ;
PREDICATE: dup-type-var < type-var order>> 0 > ;
! INSTANCE: base-type-var term-var
INSTANCE: type-var term-var
! INSTANCE: dup-type-var proper-term
M: dup-type-var args>> drop f ;

! Syntax type
GENERIC: propagate-duplication ( term -- term )
TUPLE: dup-type element ;
C: <dup-type> dup-type
INSTANCE: dup-type proper-term
M: dup-type args>> element>> 1array ;
M: dup-type from-args* drop
    first <dup-type> ;
M: dup-type lift*
    element>> lift*
    <dup-type> ;
M: dup-type occurs-free? 2drop f ;
M: dup-type propagate-duplication
    <dup-type> ;

GENERIC: propagate-drop ( term -- term )
TUPLE: drop-type element ;
INSTANCE: drop-type proper-term
C: <drop-type> drop-type
M: drop-type args>> element>> 1array ;
M: drop-type from-args*
    drop first <drop-type> ;
M: drop-type lift* nip ;
    ! element>> lift* propagate-drop ;

GENERIC: change-term-var-order ( amount term -- term )
! : propagate-duplication ( term -- term )
!     1 swap change-term-var-order ;

M: type-var change-term-var-order
    swap [ [ name>> ] [ id>> ] [ order>> ] tri ] dip
    + type-var boa ;

M: type-var propagate-duplication
    ! 1 swap change-term-var-order ;
    <dup-type> ;
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
M: type-const change-term-var-order nip ;
M: type-const propagate-duplication ;
M: type-const propagate-drop ;

TUPLE: rec-type { rec-var type-var } element ;
C: <rec-type> rec-type
INSTANCE: rec-type proper-term
! ERROR: rec-type-has-no-args rec-type ;
M: rec-type args>> drop f ; ! rec-type-has-no-args ;
M: rec-type occurs-free?
    2dup rec-var>> =
    [ 2drop f ]
    [ element>> occurs-free? ] if ;
ERROR: cannot-dup-recursive-type rec-type ;
M: rec-type change-term-var-order cannot-dup-recursive-type ;
! Note: only free args!
M: rec-type lift*
    [ [ clone ] dip
      [ rec-var>> over delete-at ] [ element>> ] bi
      lift* ]
    [ rec-var>> ] bi swap <rec-type> ;
