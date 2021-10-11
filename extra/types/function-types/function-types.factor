USING: accessors arrays ascii assocs classes combinators effects kernel lists
make math math.parser math.statistics namespaces sequences strings terms
types.base-types types.renaming types.util ;

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
    [ order>> [ number>superscript append ] unless-zero ] tri ;

M: rec-type effect>string
    [ rec-var>> effect>string
      "μ" "." surround  ]
    [ element>> effect>string append ] bi ;


M: drop-type effect>string element>> effect>string "𝓓" prepend ;

M: dup-type effect>string element>> effect>string "(" ")'" surround ;

M: type-const effect>string thing>> effect>string ;

GENERIC: effect-element>term ( element -- term )
! NOTE: This is needed so that old and new effects work together using type-of
! M: fun-type effect-element>term ;
M: type-var effect-element>term mappings get [ ensure-unique-var ] cache ;
! M: dup-type-var effect-element>term
!     -1 swap change-term-var-order effect-element>term
!     <dup-type> ;
M: proper-term effect-element>term
    [ effect-element>term ] map-args ;

: make-configuration ( elements var-element -- term )
    [ [ effect-element>term ] map <reversed> ] [  ] bi* sequence>list* ;

M: pair effect-element>term
    second effect-element>term ;

: row-effect-element>term ( element -- term )
    dup string?
    [ capitalize map-varname ]
    [ effect-element>term ] if ;

M: variable-effect effect-element>term
    {
        [ in>> ]
        [ in-var>> row-effect-element>term  make-configuration ]
        [ out>> ]
        [ out-var>> row-effect-element>term make-configuration ]
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
    element>> effect-element>term
    type-var check-instance
    1 swap change-type-var-order ;

M: drop-type effect-element>term
    element>> effect-element>term
    ! <pred> ;
    <drop> ;


! * Pred/Succ
M: pred-type effect>string
    element>> effect>string "𝓟" prepend ;
M: succ-type effect>string
    element>> effect>string "𝓢" prepend ;

! * Alternative Type

M: alt-type effect>string
    alternatives>> [ effect>string ] map "|" join
    "(" ")" surround ;

! * Linearity
! Remove alternatives whose variables are not used
: unused-var? ( counts var -- ? )
    ?of [ 2 < ] [ drop t ] if ;

! TODO: check semantics here regarding all/any usage
: unused-alternative? ( counts term -- ? )
    term-vars [ unused-var? ] with all? ;

: var-usage ( term -- counts )
    term-vars histogram ;

GENERIC: clean-up-alternatives* ( counts term -- term )
M: alt-type clean-up-alternatives*
    dupd alternatives>> [ clean-up-alternatives* ] with map
    [ unused-alternative? ] with reject
    dup length 1 = [ first ] [ <alt-type> ] if ;
M: term clean-up-alternatives* nip ;
M: proper-term clean-up-alternatives*
    [ clean-up-alternatives* ] with map-args ;

: clean-up-alternatives ( term -- term )
    [ var-usage ]
    [ clean-up-alternatives* ] bi ;

ERROR: non-linear-function-type type var ;
: assert-linear-type ( fun-type -- fun-type )
    dup var-usage [
        dup 2 >
        [ non-linear-function-type ]
        [ 2drop ] if
    ] assoc-each ;


! * Interface

: effect>term ( effect -- fun-type )
    [
        effect-element>term
    ] with-unique-names ;
