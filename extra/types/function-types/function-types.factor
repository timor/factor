USING: accessors arrays ascii assocs classes combinators effects kernel lists
make math.parser namespaces sequences strings terms types.base-types
types.renaming types.util ;

IN: types.function-types

! * Function types, which correspond to effects
! A single var type indicates that this is only the row variable
! UNION: configuration-type list type-var ;
TUPLE: fun-type
    consumption production ;
    ! { consumption list initial: +nil+ }
    ! { production list initial: +nil+ } ;

INSTANCE: fun-type proper-term
INSTANCE: fun-type effect-type
C: <fun-type> fun-type
M: fun-type args>>
    [ consumption>> ] [ production>> ] bi 2array ;
M: fun-type from-args* drop
    first2 <fun-type> ;
: configuration>string ( list -- string )
    [ list*>array [ <reversed> ] dip prefix
      [ " " % ] [ effect>string % ] interleave ] "" make ;
M: list effect>string configuration>string ;

M: fun-type propagate-duplication
    [ propagate-duplication ] map-args ;
M: fun-type propagate-drop
    [ propagate-drop ] map-args ;
! [ consumption>> ] [ production>> ] bi
! [ propagate-duplication ] lmap*
! <fun-type> ;

M: fun-type effect>string
    [
        "(" %
          [ consumption>> configuration>string % " → " % ]
          [ production>> configuration>string % ] bi
          ")" %
    ] "" make ;

M: type-var effect>string
    [ name>> ] [ id>> [ number>string append ] unless-zero ]
    [ order>> CHAR: ' <string> append ] tri ;

M: rec-type effect>string
    [ rec-var>> effect>string
      "rec(" "|" surround  ]
    [ element>> effect>string append ] bi
    ")" append ;

M: drop-type effect>string element>> effect>string "↓(" ")" surround ;

M: dup-type effect>string element>> effect>string "(" ")'" surround ;

M: type-const effect>string thing>> effect>string ;

GENERIC: effect-element>term ( element -- term )
! NOTE: This is needed so that old and new effects work together using type-of
! M: fun-type effect-element>term ;
M: type-var effect-element>term mappings get [ ensure-unique-var ] cache ;
M: dup-type-var effect-element>term
    -1 swap change-term-var-order effect-element>term
    <dup-type> ;
M: proper-term effect-element>term
    [ effect-element>term ] map-args ;

: make-configuration ( elements var-element -- term )
    [ [ effect-element>term ] map <reversed> ] [  ] bi* sequence>list* ;

M: pair effect-element>term
    second effect-element>term ;

M: variable-effect effect-element>term
    {
        [ in>> ]
        [ in-var>> capitalize map-varname make-configuration ]
        [ out>> ]
        [ out-var>> capitalize map-varname make-configuration ]
    } cleave <fun-type> ;

PREDICATE: anon-effect < effect variable-effect? not ;
M: anon-effect effect-element>term
    [ in>> ] [ out>> ] bi
    "R" 0 <type-var> ensure-unique-var
    [ make-configuration ] curry bi@
    <fun-type> ;

M: class effect-element>term
    <type-const> ;

M: string effect-element>term
    map-varname ;

M: dup-type effect-element>term
    element>> effect-element>term propagate-duplication ;
    ! <dup-type> ;

M: drop-type effect-element>term
    element>> effect-element>term propagate-drop ;

: effect>term ( effect -- fun-type )
    [
        effect-element>term
    ] with-unique-names ;
