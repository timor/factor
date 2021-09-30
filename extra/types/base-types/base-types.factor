USING: accessors assocs effects kernel math math.parser sequences strings terms
;

IN: types.base-types

FROM: namespaces => set ;

! * Atomic type variables and Primitives
TUPLE: type-var
    { name string read-only }
    { id integer read-only }
    { order integer read-only } ;
PREDICATE: base-type-var < type-var order>> 0 = ;
PREDICATE: dup-type-var < type-var order>> 0 = not ;
INSTANCE: base-type-var term-var
INSTANCE: dup-type-var proper-term
M: dup-type-var args>> drop f ;

: <type-var> ( name id -- obj )
    0 type-var boa ;

TUPLE: type-const thing ;
C: <type-const> type-const
INSTANCE: type-const proper-term
M: type-const args>> drop f ;

TUPLE: dup-type element ;
C: <dup-type> dup-type

TUPLE: drop-type element ;
C: <drop-type> drop-type

TUPLE: rec-type { rec-var type-var } element ;
C: <rec-type> rec-type
INSTANCE: rec-type proper-term
ERROR: rec-type-has-no-args rec-type ;
M: rec-type args>> rec-type-has-no-args ;
! Note: only free args!
M: rec-type lift*
    [ clone ] dip
    [ rec-var>> over delete-at ] [ element>> ] bi
    lift* ;

