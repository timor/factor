USING: accessors arrays ascii classes combinators effects kernel lists make math
sequences strings terms types.base-types types.renaming ;

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
! TODO: move to lists vocab
: list*>array ( list -- array lastcdr )
    { } swap [ dup list? ] [ uncons [ suffix ] dip ] while ;
: configuration>string ( list -- string )
    [ list*>array [ <reversed> ] dip prefix
      [ " " % ] [ effect>string % ] interleave ] "" make ;
M: list effect>string configuration>string ;

M: fun-type effect>string
    [
        "(" %
          [ consumption>> configuration>string % " → " % ]
          [ production>> configuration>string % ] bi
          ")" %
    ] "" make ;

M: type-var effect>string
    [ name>> ] [ id>> number>string append ]
    [ order>> CHAR: ' <string> append ] tri ;

M: rec-type effect>string
    [ rec-var>> effect>string
      "rec(" "|" surround  ]
    [ element>> effect>string append ] bi
    ")" append ;

M: drop-type effect>string element>> effect>string "drop(" ")" surround ;

M: dup-type effect>string element>> effect>string "dup(" ")" surround ;

M: type-const effect>string thing>> effect>string ;

GENERIC: effect-element>term ( element -- term )
! NOTE: This is needed so that old and new effects work together using type-of
M: fun-type effect-element>term ;

! TODO: move to lists vocab
: sequence>list* ( sequence lastcdr -- list )
    [ <reversed> ] dip [ swons ] reduce ;

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

GENERIC: change-term-var-order ( amount term -- term )
M: type-var change-term-var-order
    swap [ [ name>> ] [ id>> ] [ order>> ] tri ] dip
    + type-var boa ;
M: type-const change-term-var-order nip ;
M: proper-term change-term-var-order
    [ change-term-var-order ] with map-args ;

: propagate-duplication ( term -- term )
    1 swap change-term-var-order ;

M: dup-type effect-element>term
    element>> effect-element>term propagate-duplication ;

: effect>term ( effect -- fun-type )
    [
        effect-element>term
    ] with-unique-names ;
