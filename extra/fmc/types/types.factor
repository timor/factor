USING: accessors arrays assocs combinators combinators.short-circuit fmc kernel
lists make match namespaces sequences typed types.util ;

IN: fmc.types

! * Typing rules

! ** Terms
TUPLE: fmc-type in out ;
C: <fmc-type> fmc-type

! NOTE: unused?
TUPLE: type-var name ;
C: <type-var> type-var

TUPLE: row-type-var name ;
C: <row-type-var> row-type-var

INSTANCE: type-var match-var
INSTANCE: row-type-var match-var

! Special structure that can be used to match rests in lists
TUPLE: row-cons < cons-state ;
C: <row-cons> row-cons
M: \ row-cons swons* drop swap <row-cons> ;

TUPLE: composition upper lower ;
C: <composition> composition

UNION: type-term fmc-type type-var list composition ;

TYPED: add-to-consumption ( type: fmc-type tterm: type-term -- type': fmc-type )
    ! [ in>> swap suffix ]
    [ in>> cons ]
    [ out>> ] bi <fmc-type> ;

: <fresh-type-var> ( -- obj )
    "ρ" uvar <type-var> ;

TYPED: <urow-var> ( name -- var: row-type-var )
    uvar <row-type-var> ;

TYPED: <unit-type> ( -- type: fmc-type )
    "τ" <urow-var> ! nil <row-cons>
    ! dup
    [ nil cons ] keep
    <fmc-type> ;

TYPED: <unknown-type> ( -- type: fmc-type )
    "ρ" <urow-var> ! nil <row-cons>
    "σ" <urow-var> ! nil <row-cons>
    <fmc-type> ;

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

! TYPED:: solve-abs ( var: maybe{ fmc-type } cont: maybe{ fmc-type } result: maybe{ fmc-type }
!                    -- var: type-term cont-type: fmc-type result-type: fmc-type )
!     var [ <unknown-type> ] unless* :> var
!     cont [ <unknown-type> ] unless* :> cont
!     result [ var cont in>> cons cont out>> <fmc-type> ] unless* :> result
!     cont result bi-match
!     [ var replace-patterns
!       cont replace-patterns
!       result replace-patterns
!     ] with-variables ;

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


! TYPED:: solve-var ( var: type-term cont: maybe{ fmc-type } result: maybe{ fmc-type }
!                     -- var: fmc-type cont: fmc-type result: fmc-type )
!     var [ <unknown-type> ] unless* :> var
!     cont result and not [ <unknown-type> ] [ f ] if :> common
!     cont [ var out>> common in>> 2array common out>> <fmc-type> ] unless* :> cont
!     result [ var in>> common in>> 2array common out>> <fmc-type> ] unless* :> result
!     var cont unify-composition :> ( var cont )
!     cont result unify-transfer
!     ;

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

! TYPED:: solve-appl ( body: maybe{ fmc-type } cont: maybe{ fmc-type } result: maybe{ fmc-type }
!                      -- body: type-term cont: fmc-type result: fmc-type )
!     body [ <unknown-type> ] unless* :> body
!     result [ <unknown-type> ] unless* :> result
!     cont [ result [ in>> body swons ] [ out>> ] bi <fmc-type> ] unless* :> cont
!     cont result bi-match
!     [
!         body replace-patterns
!         cont replace-patterns
!         result replace-patterns
!     ] with-variables ;

DEFER: type-of*
TYPED:: type-of/abs ( cont: fmc-term lpop: loc-pop -- type: fmc-type )
    lpop var>> :> var
    var get [ <unknown-type> ] unless* :> var-type
    [ var-type var set
      cont type-of*
      var get
    ] with-scope :> ( cont-type var-type )
    cont-type [ in>> var-type swons ] [ out>> ] bi <fmc-type> ;

GENERIC: uncons-input ( in -- car cdr )
M: list uncons-input uncons ;
M: row-type-var uncons-input nil swap ;

TYPED:: type-of/app ( cont: fmc-term lpush: loc-push -- type: fmc-type )
    lpush body>> type-of* :> body-type
    cont type-of* [ in>> ] [ out>> ] bi :> ( rho+sigma tau )
    rho+sigma uncons-input :> ( rho sigma )
    body-type rho solve-eq
    [ sigma subst
      tau subst
      <fmc-type>
    ] with-variables ;
    ! sigma tau <fmc-type> ;

! : compose-type-lists ( car-types1 cdr-types2 -- types )
!     { { [ 2dup [ nil? ] both? ] [ 2drop nil ] }
!       { [ 2dup [ list? ] both? ] [ list* ] }
!       [ <composition> ]
!     } cond ;

! ERROR: ambiguous-composition type1 type2 ;
! PREDICATE: composed-output < fmc-type out>> composition? ;
! PREDICATE: composed-input < fmc-type in>> composition? ;

! Row effects:
! variable: L{ … . row-type-var }
! empty stack: L{ ... . nil }
! M: composition decompose-right
!     over composition? [ f ]
!     [ upper>> t ] if ;
! M: composition decompose-left
!     dup composition? [ f ]
!     [ [ lower>> t ] dip t ] if ;
! GENERIC: solve-composition ( type1: fmc-type type2: fmc-type -- type: fmc-type )

! TYPED: solve-strict-composition ( type1: fmc-type type2: fmc-type -- type: fmc-type )
!     [ [ out>> ] [ in>> ] bi* solve-eq drop ]
!     [ [ in>> ] [ out>> ] bi* ] 2bi ;

! TYPED:: solve-input-composition ( type1: fmc-type type2: composed-input -- type: fmc-type )
!     type1 [ in>> ] [ out>> ] :> ( rho sigma )
!     type2 [ in>> [ type1>> ] [ type2>> ] bi ] [ out>> ] :> ( rho-upsilon tau )

! M: composed-input solve-composition
!     over composed-output? [ ambiguous-composition ] when
!     solve-input-composition ;
! M: fmc-type solve-composition
!     over composed-output? [ solve-output-composition ]
!     [ solve-strict-composition ] if ;

! TYPED: solve-composition ( type1: fmc-type type2: fmc-type -- type: fmc-type )
!     { { [ 2dup [ composed-out ] ] } }
! : atom? ( obj -- ? ) list? not ;
! INSTANCE: row-cons match-var
M: row-cons decompose-right
    call-next-method
    [ car>> [ 1array ] bi@ t ] unless* ;
M: row-cons decompose-left
    call-next-method
    [ [ car>> ] dip [ 1array ] bi@ t ] unless* ;
! M: row-cons subst
!     [ car get ] keep or ;
! M: row-cons subst
!     [ get ]
ERROR: free-var cont varname ;
TYPED:: type-of/var ( cont: fmc-term var: varname -- type: fmc-type )
    ! var get [ cont var free-var ] unless* :> var-type
    ! ! cont type-of* [ in>> ] [ out>> ] bi :> ( in2 upsilon )
    ! ! var-type [ in>> ] [ out>> ] bi :> ( rho out1 )
    ! ! "σ" <urow-var> :> sigma
    ! ! "τ" <urow-var> :> tau
    ! ! sigma tau cons :> sigma-tau
    ! ! rho tau cons :> rho-tau
    ! ! sigma-tau rho-tau solve-eq
    ! ! [ rho subst sigma subst <fmc-type>
    ! !   rho-tau subst upsilon subst <fmc-type>
    ! ! ] with-variables :> ( var-type result-type )
    ! ! var-type var set
    ! ! result-type ;
    ! cont type-of* [ in>> ] [ out>> ] bi :> ( in2 out2 )
    ! var-type [ in>> ] [ out>> ] bi :> ( rho sigma )
    ! ! "σ" <urow-var> :> sigma
    ! "ττ" <urow-var> :> tau
    ! "υυ" <urow-var> nil <row-cons> :> upsilon
    ! ! sigma tau cons :> sigma-tau
    ! ! rho tau cons :> rho-tau
    ! ! sigma-tau rho-tau solve-eq
    ! sigma tau list* :> sigma-tau
    ! rho tau list* :> rho-tau
    ! sigma-tau in2 2array
    ! sigma-tau rho-tau 2array
    ! upsilon out2 2array
    ! 3array solve
    ! [ rho subst sigma subst <fmc-type>
    !   rho-tau subst upsilon subst <fmc-type>
    ! ] with-variables :> ( var-type result-type )
    ! var-type var set
    ! result-type ;
    var get [ cont var free-var ] unless* :> var-type
    var-type [ in>> ] [ out>> ] bi :> ( in1 out1 )
    cont type-of* [ in>> ] [ out>> ] bi :> ( in2 out2 )
    out1 in2 solve-eq
    [
        in1 subst :> in1'
        in1' out1 subst <fmc-type>
        in2 subst out2 subst <fmc-type>
    ] with-variables :> ( var-type result-type )
    var-type var set
    result-type ;

! TYPED: type-of* ( term: fmc-term -- type: fmc-type )
!     [ <unit-type> ] {
!         { loc-pop [ var>> context get [ drop <unknown-type> ] cache
!                     swap type-of* f solve-abs 2nip ] }
!         { varname [ context get [ drop <unknown-type> ] cache
!                     swap type-of* f solve-var 2nip ] }
!         { loc-push [ body>> type-of* swap type-of* f solve-appl 2nip ] }
!     } lmatch ;

TYPED: type-of* ( term: fmc-term -- type: fmc-type )
    [ <unit-type> ] {
        { loc-pop [ type-of/abs ] }
        { varname [ type-of/var ] }
        { loc-push [ type-of/app ] }
    } lmatch ;

! TYPED: type-of ( term: fmc-term -- type: fmc-type )
!     [ H{ } clone context [ type-of* ] with-variable ]
!     with-var-names ;

TYPED: type-of ( term: fmc-term -- type: fmc-type )
    [ type-of* ] with-var-names ;

DEFER: (build-type)
TYPED:: build/abs ( cont: fmc-term lpop: loc-pop -- type: fmc-type )
    lpop var>> :> var
    <fresh-type-var> [ var set ] keep :> var-type
    cont (build-type) :> cont-type
    "σ_abs" <urow-var> "τ_abs" <urow-var> :> ( sigma tau )
    tau cont-type out>> 2array ,
    sigma cont-type in>> 2array ,
    var-type sigma cons tau <fmc-type> ;

TYPED:: build/var ( cont: fmc-term var: varname -- type: fmc-type )
    var get dup [ var "free var" 2array throw ] unless :> var-type
    "τ_var" <urow-var> "υ_var" <urow-var> :> ( tau upsilon )
    "ρ_var" <urow-var> "σ_var" <urow-var> :> ( rho sigma )
    cont (build-type) :> cont-type
    sigma tau cons cont-type in>> 2array ,
    upsilon cont-type out>> 2array ,
    var-type rho sigma <fmc-type> 2array ,
    rho tau cons upsilon <fmc-type> ;

TYPED:: build/app ( cont: fmc-term lpush: loc-push -- type: fmc-type )
    lpush body>> (build-type) :> body-type
    cont (build-type) :> cont-type
    "σ_app" <urow-var> "τ_app" <urow-var> :> ( sigma tau )
    body-type sigma cons cont-type in>> 2array ,
    tau cont-type out>> 2array ,
    sigma tau <fmc-type> ;

TYPED: (build-type) ( term: fmc-term -- type: fmc-type )
    [ <unit-type> ] {
        { varname [ build/var ] }
        { loc-pop [ build/abs ] }
        { loc-push [ build/app ] }
    } lmatch
    ;

TYPED: build-type ( term: fmc-term -- type: fmc-type problem )
    [ [ (build-type) ] { } make ] with-var-names ;


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
