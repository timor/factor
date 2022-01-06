USING: accessors assocs fmc kernel lists match namespaces typed types.util ;

IN: fmc.types

! * Typing rules

! ** Terms
TUPLE: fmc-type in out ;
C: <fmc-type> fmc-type

TUPLE: type-var name ;
C: <type-var> type-var
TUPLE: row-type-var name ;
C: <row-type-var> row-type-var

INSTANCE: type-var match-var
INSTANCE: row-type-var match-var

UNION: type-term fmc-type type-var list ;

TYPED: add-to-consumption ( type: fmc-type tterm: type-term -- type': fmc-type )
    ! [ in>> swap suffix ]
    [ in>> cons ]
    [ out>> ] bi <fmc-type> ;

: <fresh-type-var> ( -- obj )
    "ρ" uvar <type-var> ;

TYPED: <unit-type> ( -- type: fmc-type )
    "τ" uvar <row-type-var> dup <fmc-type> ;

TYPED: <unknown-type> ( -- type: fmc-type )
    "σ" uvar <row-type-var>
    "υ" uvar <row-type-var> <fmc-type> ;

! TYPED: <pop-type> ( -- type: fmc-type )
!     <
!     ! nil <fresh-type-var> 1list <fmc-type> ;

SYMBOL: context

! TYPED: solve-unit ( in: maybe{ list } out: maybe{ list } -- in: type-term out: type-term )
!     { { [ 2dup and ] [ type-and dup ] }
!       { [ 2dup or not ] [ 2drop <row-type-var> dup ] }
!       [ or dup ]
!     } cond ;

! Like matching, but if we create var->var bindings, also store the inverse
: bi-match ( value1 value2 -- bindings   )
    match
    [ [ 2dup swap ,,
        dup match-var? [ ,, ] [ 2drop ] if
      ] assoc-each ] H{ } make ;

TYPED:: solve-abs ( var: maybe{ fmc-type } cont: maybe{ fmc-type } result: maybe{ fmc-type }
                   -- var: type-term cont-type: fmc-type result-type: fmc-type )
    var [ <unknown-type> ] unless* :> var
    cont [ <unknown-type> ] unless* :> cont
    result [ var cont in>> cons cont out>> <fmc-type> ] unless* :> result
    cont result bi-match
    [ var replace-patterns
      cont replace-patterns
      result replace-patterns
    ] with-variables ;

: list-end? ( thing -- ? )
    { [ nil? ] [ list? not ] } 1|| ;

: (match-consumption) ( out-types1 target -- tail )
    { { [ dup list-end? ] [ drop ] }
      { [ over list-end? ] [ nip ] }
      [ [ unswons ] bi@ swapd bi-match %% (match-consumption) ]
    } cond ;

: match-consumption ( out-types1 target -- tail bindings )
    [ (match-consumption) ] H{ } make ;

! TUPLE: type-comp types1 types2 ;
! C: <type-comp> type-comp
! UNION: composition type-term type-comp ;

! TYPED: unify-compositions ( t1: composition t2: composition -- t1 )
! ! Matching of composition:
! ! out1.τ = A
! ! in1.*t = A

! : unify-lists ( list1 list2 -- list1 list2 )
!     2dup match
!     [ [ replace-patterns ] bi@ ] with-variables ;


! :: solve-composition ( in1 out1 target -- in1 out1 target tail )
!     target list?
!     [ in1 target unify-lists out1 unify-lists tail ]
!     [  ]

! : concat-types ( types1 types2 -- types )
!     2dup [ list? not ]
!     dup list? not [ drop ]
!     [ over list? not [ nip ] ] ;


! If we know the difference of the composed type, then we need to specify the
! padding.  Otherwise, we want to actually derive the difference
! TYPED: type-height ( type: fmc-type -- n: integer )
!     [ out>> length ] [ in>> length ] bi - ;
: adjust-composition ( types1 types2 -- types1 types2 )
    { { [ 2dup [ row-type-var? ] both? ] [ ] }
      { [ 2dup [ pair? ] both? ] [ "matching unknown composition" 3array throw ] }
      { [ over row-type-var? ] [ [ nil 2array ] dip ] }
      { [ dup row-type-var? ] [ nil 2array ] }
    } cond ;

: match-composition ( types1 types2 -- bindings )
    adjust-composition bi-match ;

: clean-composition ( types -- types )
    dup pair?
    [ [ nil? ] reject dup length 1 = [ first ] when ] when ;

: clean-fmc-type ( fmc-type -- fmc-type )
    [ in>> ] [ out>> ] bi
    [ clean-composition ] bi@ <fmc-type> ;

TYPED: unify-composition ( type1: fmc-type type2: fmc-type -- type1: fmc-type type2: fmc-type )
    2dup [ out>> ] [ in>> ] bi* match-composition
    [ [ replace-patterns ] bi@ ] with-variables ;

TYPED: unify-transfer ( type1: fmc-type type2: fmc-type -- type1: fmc-type type2: fmc-type )
    2dup [ in>> ] bi@ match-composition
    [ [ replace-patterns ] bi@ ] with-variables
    2dup [ out>> ] bi@ match
    [ [ replace-patterns ] bi@ ] with-variables ;


TYPED:: solve-var ( var: type-term cont: maybe{ fmc-type } result: maybe{ fmc-type }
                    -- var: fmc-type cont: fmc-type result: fmc-type )
    var [ <unknown-type> ] unless* :> var
    cont result and not [ <unknown-type> ] [ f ] if :> common
    cont [ var out>> common in>> 2array common out>> <fmc-type> ] unless* :> cont
    result [ var in>> common in>> 2array common out>> <fmc-type> ] unless* :> result
    var cont unify-composition :> ( var cont )
    cont result unify-transfer

    ! [ var out>> cont in>> match-composition %%
    !   cont out>> result out>> match %%
    !   cont in>> result in>> match-composition %%
    !   var in>> result in>> match-composition %%
    ! ] H{ } make
    ! [
    !     var replace-patterns clean-fmc-type
    !     cont replace-patterns clean-fmc-type
    !     result replace-patterns clean-fmc-type
    ! ] with-variables ;

TYPED:: solve-appl ( body: maybe{ fmc-type } cont: maybe{ fmc-type } result: maybe{ fmc-type }
                     -- body: type-term cont: fmc-type result: fmc-type )
    body [ <unknown-type> ] unless* :> body
    result [ <unknown-type> ] unless* :> result
    cont [ result [ in>> body swons ] [ out>> ] bi <fmc-type> ] unless* :> cont
    cont result bi-match
    [
        body replace-patterns
        cont replace-patterns
        result replace-patterns
    ] with-variables ;

TYPED: type-of* ( term: fmc-term -- type: fmc-type )
    [ <unit-type> ] {
        { loc-pop [ var>> context get [ drop <unknown-type> ] cache
                    swap type-of* f solve-abs 2nip ] }
        { varname [ context get [ drop <unknown-type> ] cache
                    swap type-of* f solve-var 2nip ] }
        { loc-push [ body>> type-of* swap type-of* f solve-appl 2nip ] }
    } lmatch ;

TYPED: type-of ( term: fmc-term -- type: fmc-type )
    [ H{ } clone context [ type-of* ] with-variable ]
    with-var-names ;

! GENERIC: in>out ( in-types term: fmc-term -- in-types )
! GENERIC: in<out ( out-types term: fmc-term -- in-types )
! TYPED: in>out ( type: fmc-type term: fmc-term -- type: fmc-type )
!     [  ] {
!         { loc-pop [ [ var>> ] ] }
!     }
!     lmatch ;
! TYPED: in<out ( out-types term: fmc-term -- in-types )
!     [  ] {
!     } lmatch ;

! DEFER: type-of
! TYPED: type-of/abs ( cont: fmc-term lpop: loc-pop -- type: type-term )
!     var>> context get ?at
!     [ [ drop <pop-type> ] cache ] unless
!     swap
!     [ type-of ] dip add-to-consumption ;

! TYPED:: unify-type-stacks ( list1: list list2: list -- list: list bindings: assoc )
!     {
!         { [ list1 nil? ] [ list2 nil? [ nil f ] [ swap unify-type-stacks ] if ] }
!         { [ list2 nil? ] [ list1 bindings ] }
!         [ list1 uncons :> ( car1 cdr1 )
!           list2 uncons :> ( car2 cdr2 )

!         ]
!     } cond ;


! NOTE: simply assuming match by definition here, no unification!
! TYPED:: unify-composition ( cont-type: fmc-type var-type: fmc-type -- type )
!     type1 [ in>> ] [ out>> ] bi :> in1 out1
!     type2 [ in>> ] [ out>> ] bi :> in2 out2
!     out1 in2 2dup [ length ] bi@ - :> diff
!     diff 0 >
!     [ in1 in2 diff head* ]


! TYPED: type-of/var ( current-type: cont: fmc-term var: varname -- type: fmc-type )
!     context get at dup [ "free variable" throw ] unless
!     swap type-of*


! TYPED: type-of* ( current-type: fmc-type term: fmc-term -- type: fmc-type )
!     [ ]
!     {
!         { loc-pop [ type-of/abs ] }
!         { varname [ type-of/var ] }
!         { loc-push [ type-of/appl ] }
!     } lmatch

! TYPED: decompose-problem ( term: fmc-term -- type: fmc-type constraints )
