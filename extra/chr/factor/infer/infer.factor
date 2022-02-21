USING: accessors chr chr.factor chr.factor.conditions chr.factor.control
chr.parser chr.state kernel sequences terms ;

IN: chr.factor.infer


! * Scope Inference
! Responsible for stepping through new scope

! TUPLE: Infer < chr-pred beg s quot ;
TUPLE: Infer < trans-pred quot ;
TUPLE: InferBetween < trans-pred quot ;
TUPLE: EndInferScope < chr-pred last-sub ;
! Need to save between exec and next one
TUPLE: InferNext < state-pred cur next word rest ;

CHRAT: infer-factor { InferBetween }
IMPORT: control-flow

CHR: start-infer @ { InferBetween ?r ?t ?q } // -- [ ?q known? ] |
{ Stack ?r ?rho }
{ Stack ?s ?rho }
{ Scope ?r ?t { ?s } }
{ Infer ?r ?s ?q } ;

! CHR: abort-infer @ { AbsurdState ?r } // { InferBetween ?r __ __ } { Infer ?r __ __ } -- | ;

CHR: end-infer @ // { InferBetween ?r ?t ?q } { Infer ?r ?x [ ] } -- |
{ Stack ?x ?rho } { Stack ?t ?rho }
! { CleanScope ?r ?t }
{ EndInferScope ?x } ;

CHR: infer-step @
{ InferBetween ?r ?t __ }
//
{ Infer ?r ?s ?q } -- [ ?q known? ] | [| |
                                           ?s seq-state :> sn
                                           ?q unclip-slice :> ( rest w )
                                           { InferNext ?r ?s sn w rest }
                                      ] ;
CHR: infer-next-word @ { InferNext ?r ?s ?t ?w ?q } // -- | [| |
    ?w wrapper? [ ?w wrapped>> :> x { Push ?s ?t x } ]
    [ { Exec ?s ?t ?w } ] if
] ;

CHR: infer-next-rest @ // { InferNext ?r __ ?t ?w ?q } -- |
    { AddLink ?r ?t }
    { Infer ?r ?t ?q } ;
! [| | ?q unclip :> ( rest w ) ?s seq-state :> sn
!  w wrapper?
!  [ w wrapped>> :> x { Push ?s sn x } ]
!  [ { Exec ?s sn w } ] if :> action
!  { { AddLink ?r sn }
!    action
!    { Infer ?r sn rest }
!  }
! ] ;




;
