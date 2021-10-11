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

M: type-const effect>string thing>> name>> ;

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

! * Choice Types

M: sum-type effect>string
    alternatives>> [ effect>string ] map "/" join
    "(" ")" surround ;

M: all-type effect>string
    alternatives>> [ effect>string ] map " ⊕ " join
    "(" ")" surround ;

M: maybe-type effect>string
    [ type>> effect>string ]
    [ condition>> effect>string "[!" "]" surround ] bi append ;

! * Linearity
! Remove alternatives whose variables are not used
: unused-var? ( counts var -- ? )
    ?of [ 2 < ] [ drop t ] if ;

! TODO: check semantics here regarding all/any usage
: unused-alternative? ( counts term -- ? )
    term-vars [ unused-var? ] with all? ;

: var-usage ( term -- counts )
    term-vars histogram ;

SINGLETON: +any+
INSTANCE: +any+ proper-term
M: +any+ args>> drop f ;
M: +any+ effect>string drop "⋆" ;
M: +any+ effect-element>term ;

! All type variables that don't appear twice (except for conds of maybe-types,
! which may appear at least thrice) Are replaced by wildcards.  This should
! ensure keeping linear types
! TODO: might need to handle maybe-type case specially?
GENERIC: mark-unused ( counts term -- term )
M: term-var mark-unused
    [ unused-var? ] keep swap
    [ drop +any+ ] when ;
M: proper-term mark-unused
    [ mark-unused ] with map-args ;

! Note that this may be needed multiple times!
GENERIC: sweep-unused ( term -- changed? term )
M: proper-term sweep-unused
    f swap [ sweep-unused [ or ] dip ] map-args
    dup args>> [ f ] [ [ +any+? ] all? ] if-empty
    [ 2drop t +any+ ] when ;
M: term-var sweep-unused f swap ;
: sweep-fun-type ( changed? term -- changed? term )
    dup production>> +any+? [ 2drop t +any+ ] when ;
M: fun-type sweep-unused
    call-next-method
    dup fun-type? [ sweep-fun-type ] when ;
: sweep-sum-type ( changed? term -- changed? term )
    dup alternatives>> [ +any+? ] any?
    [ [ drop t ]
      [ alternatives>> [ +any+? ] reject
        dup length 1 = [ first ] [ <sum-type> ] if
      ] bi* ] when ;
M: sum-type sweep-unused
    call-next-method
    dup sum-type? [ sweep-sum-type ] when ;
M: maybe-type sweep-unused
    call-next-method
    dup condition>>
    { { [ dup f-type? ] [ 3drop t +any+ ] }
      { [ dup +any+? ] [ drop [ drop t ] [ type>> ] bi* ] }
      [ drop ]
    } cond ;

: cleanup-unused ( term -- term changed? )
    [ var-usage ]
    [ mark-unused ] bi
    sweep-unused swap ;

: cleanup-fun-type ( term -- term )
    [ cleanup-unused ] loop ;

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
