USING: accessors arrays assocs chr chr.factor combinators.short-circuit effects
kernel make sequences strings terms words ;

IN: chr.factor.words

! * Constraint protocol
GENERIC: tell-chr* ( word -- body )
M: object tell-chr* drop f ;

: tell-chr ( si so word -- body )
    [ tell-chr* ] curry with-states ;

GENERIC: element>decl ( elt -- name type )
M: string element>decl drop f f ;
M: pair element>decl
    first2 dup object =
    [ 2drop f f ] [
        [ [ "anon" uvar ] unless* ] dip
    ] if ;

: row-decls ( elts -- seq )
    <reversed> [ swap element>decl [ 3array ] [ 2drop f ] if* ] map-index sift ;

: effect-elt-decls ( effect -- in out )
    [ in>> row-decls ]
    [ out>> row-decls ] bi ;

: make-type-preds ( state specs -- )
    [| | first3 :> ( s i v d )
     v "v" prepend <term-var> :> v
     { Val s i v } ,
     { ExpectInstance v d } ,
    ] with each ;

: effect>type-preds ( sin sout e -- seq )
    [ effect-elt-decls swapd [ make-type-preds ] 2bi@ ]
    { } make ;

! : effect>stack-preds ( sin sout e -- seq )
!     [ in>> length dup 0 = [ 3drop f ] [ ShiftPop boa ] if ]
!     [ out>> length dup 0 = [ 3drop f ] [ ShiftPush boa ] if ] 3bi 2array sift
!     ;

! : effect>preds ( sin sout e -- seq )
!     [ effect>type-preds ]
!     [ effect>stack-preds ] 3bi append ;

: elt>genvar ( assoc elt -- elt )
    dup pair? [ first ] when of ;

:: effect>genvars ( e -- vars in out )
    e define-term-vars
    [ [ drop dup uvar <term-var> ] assoc-map ] with-var-names
    :> vars

    e in>> <reversed> [ vars swap elt>genvar ] map :> in
    e out>> <reversed> [ vars swap elt>genvar ] map :> out
    vars in out ;

! :: word>preds ( sin sout w -- seq )
!     sin sub-state :> s1
!     w stack-effect effect>genvars :> ( vars in out )
!     vars values
!     sin s1 in Pops boa
!     s1 sout out Pushes boa 2array
!     <generator> 1array ;

:: make-word-rule ( body sin sout word -- chr )
    sin sout word Word boa 1array f
    body chr new-prop-chr ;

! M: word tell-chr*
!     [ state-in state-out ] dip
!     {
!         ! [ word>preds ]
!         [ stack-effect AssumeEffect boa ]
!     } cond ;

! M:: \ if tell-chr* ( word -- constraints )
!     state-in :> si
!     state-out :> so
!     ! si so [ word call-next-method 1array ] with-states
!     si sub-state :> s1
!     ! new-state :> s2
!     ! new-state :> s3
!     ! CHR{
!     !     { Word si so if } // -- |
!         GEN[ ( cond then: ( ..a1 -- ..b ) else: ( ..a2 -- ..c ) -- )
!              ! { Word si so if }
!              ! { Pops si s1 { else then cond } }
!              ! { Pop si s2 then }
!              ! { Pop si  }
!              { Val si 2 cond }
!              { Val si 1 then }
!              { Val si 0 else }
!              ! { Instance cond boolean }
!              { BranchIf s1 so cond a1 a2 }
!              { InferUnknown a1 b then }
!              { InferUnknown a2 c else }
!            ]
!     ! }
!     1array ;

! M:: \ call tell-chr* ( word -- constraints )
!     state-in :> si
!     state-out :> so
!     si sub-state :> s1
!     GEN[ ( q -- )
!          { Pop si s1 q }
!          { Call s1 so q }
!     ] 1array ;

GENERIC: chrat-effect ( word -- effect )
CONSTANT: effect-overrides H{
    { dip ( ..a x quot: ( ..a -- ..b ) -- ..b x ) }
    { call ( ..a quot: ( ..a -- ..b ) -- ..b ) }
}
M: word chrat-effect
    { [ effect-overrides at ] [ stack-effect ] } 1|| ;
