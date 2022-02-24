USING: accessors arrays chr chr.factor chr.factor.control chr.factor.stack
chr.modular chr.parser chr.state kernel sequences terms vectors ;

IN: chr.factor.infer


! * Scope Inference
! Responsible for stepping through new scope

! TUPLE: Infer < chr-pred beg s quot ;
TUPLE: Infer < trans-pred quot ;
! TUPLE: InferBetween < trans-pred quot ;
TUPLE: InferBetween < trans-pred quot states ;
TUPLE: EndInferScope < chr-pred last-sub ;
! Need to save between exec and next one
TUPLE: InferNext < state-pred cur next word rest ;

CHRAT: infer-factor { InferBetween }
IMPORT: control-flow

CHR: start-infer @ // { InferBetween ?r ?t ?q f } -- [ ?q known? ] { Stack ?r ?rho } |
! { Stack ?r ?rho }
! { Scope ?r ?t { ?s } }
[| | ?s 1vector :> l { InferBetween ?r ?t ?q l } ]
{ Infer ?r ?s ?q }
{ Stack ?s ?rho } ;

! CHR: abort-infer @ { AbsurdState ?r } // { InferBetween ?r __ __ } { Infer ?r __ __ } -- | ;

! CHR: modal-end-infer @ // { ask { InferBetween ?r ?t ?q } } { Infer ?r ?x [ ] } -- |
! { entailed { InferBetween ?r ?t ?q } } ;

! CHR: end-infer @ { InferBetween ?r ?t ?q ?l } // { Infer ?r ?x [ ] } -- |
! { Stack ?x ?rho } { Stack ?t ?rho } ;
CHR: end-infer @ // { InferBetween ?r ?t ?q ?a } { ask { InferBetween ?r ?t ?q ?l } } { Infer ?r ?x [ ] } -- { Stack ?x ?sig } |
! { Stack ?x ?rho } { Stack ?t ?rho }
{ EndStack ?t ?sig }
[ ?l ?a >array ==! ]
{ entailed { InferBetween ?r ?t ?q ?l } }
    ;
! { CleanScope ?r ?t }
! { EndInferScope ?x } ;

CHR: modal-infer-start @ { ask { InferBetween ?r ?t ?q __ } } // -- |
{ InferBetween ?r ?t ?q f } ;

CHR: infer-step @
{ InferBetween ?r ?t __ __ }
//
! { InferBetween ?r ?t __ ?l }
{ Infer ?r ?s ?q } -- [ ?q empty? not ]
| [| |
   ?s seq-state :> sn
   ?q unclip-slice :> ( rest w )
   { InferNext ?r ?s sn w rest }
  ] ;

! NOTE: We cut this into a two-step rule, because an Exec might render the whole branch invalid
CHR: infer-next-word @ { InferNext ?r ?s ?t ?w ?q } // -- | [| |
    ?w wrapper? [ ?w wrapped>> :> x { Push ?s ?t x } ]
    [ { Exec ?s ?t ?w } ] if
] ;

CHR: infer-next-rest @ { InferBetween ?r __ __ ?l } // { InferNext ?r __ ?t __ ?q } -- |
    ! { AddLink ?r ?t }
[ ?t ?l push f ]
{ Infer ?r ?t ?q } ;

! Link interface
CHR: link-infer-up @ { InferBetween ?r __ __ ?l } // { Link ?s ?u } -- | { Link ?r ?u } ;


;
