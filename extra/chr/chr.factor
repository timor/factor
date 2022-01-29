USING: accessors arrays combinators combinators.short-circuit kernel lexer logic
logic.private namespaces parser prettyprint.custom sequences sets typed
types.util ;

IN: chr

! * Constraint Handling Rules

! Constraint store: Sequence of constraints denoting a conjunction
! ⟨F,E,D⟩ where F: Goal Store, D, E, accumulator/simplifier Store

! MIXIN: chr-constraint
! MIXIN: builtin-constraint
! UNION: constraint chr-constraint builtin-constraint ;

SYMBOL: theory
! HOOK: apply-builtin theory ( B D -- D2 ? )
HOOK: builtin-applies? theory ( G -- ? )
HOOK: builtin-constraint? theory ( constraint -- ? )
: chr-constraint? ( obj -- ? )
    builtin-constraint? not ; inline

! M: f apply-builtin swap suffix t ;
! M: f builtin-applies? call( -- ? ) ;
GENERIC: apply-builtin ( F E D B -- F E D ? )
TUPLE: eq v1 v2 ;
M:: eq apply-builtin ( F E D B -- F E D ? )
    B [ v1>> ] [ v2>> ] bi 2array 1array :> subst
    F E [ subst lift ] bi@ D B prefix t ;
M: f builtin-constraint? eq? ;
M: f builtin-applies?
    { [ eq? ] [ [ v1>> ] [ v2>> ] bi = ] } 1&& ;

SINGLETON: factlog-theory
M: factlog-theory builtin-constraint?
    dup sequence? [ ?first ] when
    get logic-pred? ;

M:: factlog-theory apply-builtin ( F E D B -- F E D ? )
    B fact F E D B prefix t ;

! M: factlog-theory builtin-applies?

PREDICATE: builtins < sequence [ builtin-constraint? ] all? ;
PREDICATE: chrs < sequence [ chr-constraint? ] all? ;

TUPLE: chr heads nkept guard body ;
PREDICATE: propagate-chr < chr remove>> empty? ;
SLOT: keep
SLOT: remove
: keep/remove ( chr -- seq seq )
    [ heads>> ] [ nkept>> ] bi cut-slice ; inline
M: chr keep>> ( chr -- seq )
    keep/remove drop ; inline
M: chr remove>> ( chr -- seq )
    keep/remove nip ; inline

TYPED:: chr-solve ( F E: chrs D: builtins -- F E: chrs D: builtins ? )
    F unclip :> ( F2 B )
    F2 E D B apply-builtin ;
    ! ok [ F2 E D2 t ]
    ! [ F E D f ] if ;

TYPED:: chr-introduce ( F E: chrs D: builtins -- F E: chrs D: builtins ? )
    F unclip :> ( F2 C )
    F2 E C prefix D t ;

SYMBOL: chr-trace
: save-record ( H: chr F -- )
    over propagate-chr?
    [ 2array chr-trace [ swap suffix ] change ]
    [ 2drop ] if ;

: recursive-apply? ( H: chr F -- ? )
    over propagate-chr?
    [ 2array chr-trace get in? ]
    [ 2drop f ] if ;

:: find-heads ( Hs E without subst! -- subst inds )
    Hs [ subst f ]
    [ unclip-slice :> ( r h )
      E [| H i | i without in? [ f ]
         [ subst h H 2array 1array solve-next [ subst! t ] [ f ] if* ] if
        ] find-index :> ( i h2 )
      i [ r E without { i } union subst find-heads i suffix ] [ f f ] if
    ] if-empty ;

! Return Store with removed occurrences, indicate if successful
TYPED:: try-rule-match ( H: chr E: chrs -- E B/? )
    H keep>> E f f find-heads :> ( sk ik )
    H remove>> E ik sk find-heads :> ( sr ir )
      { [ sr ]
        [ H ik ir union E nths recursive-apply? not ]
      } 0&&
      [
          H guard>> [ sr lift builtin-applies? ] all? [
              ir ik diff E remove-nths
              H body>> dup t = [ drop f ] [ [ sr lift ] map ] if
              H ik ir union E nths save-record
      ] [ E f ] if
    ] [ E f ] if
    ;

: chr-solve? ( F E: chrs D: builtins -- F E: chrs D: builtins ? )
    pick [ f ] [ first builtin-constraint? ] if-empty ;

: chr-introduce? ( F E D -- F E D ? )
    pick [ f ] [ first chr-constraint? ] if-empty ;

:: find-apply ( P F E! D -- P F E D rule/? )
    f :> B!
    P [ E try-rule-match [ B! E! t ] [ drop f ] if* ] find drop
    [
      ! TODO: append?
        F B union :> F2
        F2 F = [ P F E D f ]
      [ P F2 E D t ] if
    ] [ P F E D f ] if ;

TYPED: chr-step ( P F E: chrs D: builtins -- P F E: chrs D: builtins ? )
    { { [ chr-solve? ] [ chr-solve ] }
      { [ chr-introduce? ] [ chr-introduce ] }
      [ find-apply ]
    } cond ;

: with-chr-trace ( quot -- )
    [ f chr-trace ] dip with-variable ; inline

: parse-array ( end -- seq )
    parse-until [ f ] [ >array ] if-empty ; inline

SYMBOLS: | -- // ;
SYNTAX: CHR{ \ // parse-array \ -- parse-array \ | parse-array \ } parse-array [ t ] when-empty chr boa suffix! ;
SYNTAX: ={ scan-object scan-object "}" expect eq boa suffix! ;

M: eq pprint* pprint-object ;
M: eq pprint-delims drop \ ={ \ } ;
M: eq >pprint-sequence [ v1>> ] [ v2>> ] bi 2array ;

: pprint-chr ( chr -- )
    <flow \ CHR{ pprint-word
    { [ keep>> pprint-elements \ // pprint-word ]
      [ remove>> pprint-elements \ -- pprint-word ]
      [ guard>> pprint-elements \ | pprint-word ]
      [ body>> dup t = [ drop ] [ pprint-elements ] if ]
    } cleave
    \ } pprint-word block> ;

M: chr pprint* pprint-chr ;
