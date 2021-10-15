USING: accessors arrays ascii assocs classes combinators effects formatting
kernel lists make math math.parser math.statistics namespaces sequences sets strings
terms types.base-types types.renaming types.util ;

IN: types.function-types

FROM: namespaces => set ;
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
M: +nil+ effect>string drop "" ;

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

M: type-const effect>string thing>> [ spprint "'" prepend ] [ "𝐅" ] if* ;

GENERIC: effect-element>term ( element -- term )
! NOTE: This is needed so that old and new effects work together using type-of
! M: fun-type effect-element>term ;
M: type-var effect-element>term mappings get [ ensure-unique-var ] cache ;
! M: dup-type-var effect-element>term
!     -1 swap change-term-var-order effect-element>term
!     <dup-type> ;
M: proper-term effect-element>term
    [ effect-element>term ] map-args ;

! NOTE: this here is value level!!! Right now, type-const f and f is treated identically
M: f effect-element>term <type-const> ;
M: f-type effect>string drop "𝐅" ;

: finite-effect>configurations ( effect -- consumption production )
    [ in>> ] [ out>> ] bi
    [ <reversed> "A" sequence>list* ] bi@ ;

: make-configuration ( elements var-element -- term )
    [ [ effect-element>term ] map <reversed> ] [  ] bi* sequence>list* ;

M: pair effect-element>term
    second effect-element>term ;
    ! first2 [ effect-element>term ] bi@
    ! <subtype> ;

: row-effect-element>term ( element -- term )
    dup string?
    [ capitalize map-varname ]
    [ effect-element>term ] if ;

M: variable-effect effect-element>term
    {
        [ in>> ]
        [ in-var>> row-effect-element>term make-configuration ]
        [ out>> ]
        [ out-var>> row-effect-element>term make-configuration ]
    } cleave
    ! [ <contravariant> ] [ <covariant> ] bi*
    <fun-type> ;

PREDICATE: anon-effect < effect variable-effect? not ;
M: anon-effect effect-element>term
    [ in>> ] [ out>> ] bi
    "R" 0 <type-var> ensure-unique-var
    [ make-configuration ] curry bi@
    ! [ <contravariant> ] [ <covariant> ] bi*
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

GENERIC: conditional-effect>string ( conditional-type -- condition-string )

M: conditional-type effect>string
    [ type>> effect>string ]
    [ conditional-effect>string "[" "]" surround ] bi append ;

M: maybe-type conditional-effect>string
    condition>> effect>string "!" prepend ;

M: subtype effect>string
    [ typee>> effect>string ]
    [ supertype>> effect>string ] bi "⊆" glue ;

! * Linearity
! Remove alternatives whose variables are not used
: unused-var? ( counts var -- ? )
    ! type-var-key ?of [ 2 < ] [ drop t ] if ;
    ?of [ 2 < ] [ drop t ] if ;

! TODO: check semantics here regarding all/any usage
! TBR
: unused-alternative? ( counts term -- ? )
    term-vars [ unused-var? ] with all? ;

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
! type[!a] -> type[!a]
! type[!'f] -> +any+
! type[!'1] -> type

! Neutral element for xor-type is f?
M: maybe-type sweep-unused
    call-next-method
    dup condition>>
    { { [ dup f-type? ] [ 3drop t +any+ ] }
      ! { [ dup type-const? ]
      !   [ drop [ drop t ] [ type>> ] bi* ] }
      { [ dup +any+? ] [ drop [ drop t ] [ type>> ] bi* ] }
      [ drop ]
    } cond ;

! TODO: possibly that can already be done in the unifier?
: cleanup-unused ( term -- term changed? )
    [ var-usage ]
    [ mark-unused ] bi
    sweep-unused swap ;

: cleanup-fun-type ( term -- term )
    [ cleanup-unused ] loop ;

! GENERIC: linearize-fun-type
GENERIC: source-vars ( fun-type -- seq )
M: proper-term source-vars
    { } swap [ source-vars union ] each-arg ;
M: fun-type source-vars
    consumption>> source-vars ;
M: term-var source-vars 1array ;
! : duplicate-usage ( fun-type -- assoc )
!     production>> var-usage
!     [ consumption>> term-vars members ] [ production>> var-usage ] bi
!     [ 1 > ] filter-values
!     extract-keys ;

! : linearize-term ( term -- term )
!     dup var-usage

ERROR: non-linear-function-type type var ;
: assert-linear-type ( fun-type -- fun-type )
    dup var-usage [
        dup 2 >
        [ non-linear-function-type ]
        [ 2drop ] if
    ] assoc-each ;

! C: <blackbox-type> blackbox-type
! M: blackbox-type from-args* word>>
!     [ first2 ] dip <blackbox-type> ;
! M: blackbox-type term-vars
!     [ consumption>> list*>array drop [ term-vars ] gather ]
!     [ production>> term-vars append ] bi dup append ;
! M: blackbox-type effect>string
!     [ consumption>> configuration>string ]
!     [ word>> name>> " " " " surround append ]
!     [ production>> configuration>string append ] tri
!     "[" "]" surround ;


! TUPLE: blackbox-type word input-fun-type output-fun-type ;
! C: <blackbox-type> blackbox-type ;
! INSTANCE: blackbox-type proper-term
! M: blackbox-type args>>
!     [ input-fun-type>> ]
!     [ output-fun-type>> ] bi 2array ;
!     wrapper-type>> 1array ;
! M: blackbox-type from-args*
!     word>> swap first2 <blackbox-type> ;
! : blackbox-effect-string ( blackbox-type -- string )
!     [ input-fun-type>> production>> configuration>string ]
!     [ word>> name " " dup surround append ]
!     [ output-fun-type>> consumption>> configuration>string append ] tri
!     "[" "]" surround ;
! M: blackbox-type effect>string
!     [ input-fun-type>> consumption>> configuration>string ]
!     [ blackbox-effect-string " " dup surround append ]
!     [ output-fun-type>> production>> configuration>string append ] tri
!     "(" ")" surround ;
! M: blackbox-type args>>
!     [ inputs>> ] [ outputs>> ] bi append ;
! M: blackbox-type from-args* word>>
!     [ first2 ] dip word>> <primitive-type> ;
! M: blackbox-type type-variance
!     [ inputs>> ] [ outputs>> ] bi
!     [ length +contra+ <array> ]
!     [ length +co+ <array> ] bi* append ;

! M: blackbox-type effect>string
!     [ word>> name>> "[" "]" surround ]
!     [ call-next-method ] bi append ;
!     ! [ args-effect-strings ] bi " " join "(" ")" surround append ;


! * Variance

M: fun-type type-variance
    drop { +contra+ +co+ } ;

GENERIC: variance>string ( variance -- string )
M: +in+ variance>string drop "⁼" ;
M: +co+ variance>string drop "⁺" ;
M: +contra+ variance>string drop "⁻" ;

: args-effect-strings ( type -- seq )
    [ type-variance ] [ args>> ] bi
    [ [ variance>string ] [ effect>string ] bi* append ] 2map ;

M: proper-term effect>string
    [ class-of name>> ] [ args-effect-strings ] bi
    " " join " " prepend append "T{" "}" surround ;

! * Variable depth
! Having more row effects than one is not allowed usually.  So we need to insert
! a marker when unifying.
! TUPLE: macro-call n quot args ;
! C: <macro-type> macrro
! INSTANCE: macro-type proper-term
! M: macro-type args>> drop f ;

! * Some printing
M: choice-type effect>string
    [ cond>> effect>string "?[" append ]
    [ then>> effect>string ":" append append ]
    [ else>> effect>string append "]" append ] tri ;


! * Interface

: effect>term ( effect -- fun-type )
    [
        effect-element>term
    ] with-unique-names ;
