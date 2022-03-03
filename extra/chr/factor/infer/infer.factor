USING: accessors chr chr.factor chr.factor.control chr.parser chr.state kernel
sequences terms vectors words ;

IN: chr.factor.infer


! * Scope Inference
! Responsible for stepping through new scope

! TUPLE: Infer < chr-pred beg s quot ;
TUPLE: Infer < trans-pred quot ;
! TUPLE: InferBetween < trans-pred quot ;
TUPLE: InferBetween < trans-pred quot ;
TUPLE: EndInferScope < chr-pred last-sub ;
! Need to save between exec and next one
TUPLE: InferNext < trans-pred word rest ;
TUPLE: InferScope < Scope quot next ;
TUPLE: Inferred < state-pred next rest ;
TUPLE: InsertStates < chr-pred r new ;

CHRAT: infer-factor { InferBetween }
IMPORT: control-flow

CHR: start-infer-scope @ // { InferBetween ?r ?u ?q } -- { Stack ?r ?rho } |
    { Stack ?s ?rho }
    [| | ?s 1vector :> sub { InferScope ?r ?u ?rho ?sig sub ?q ?s } ]
    ! { InferScope ?r ?u ?rho ?sig { ?s } ?q ?s }
 ;

CHR: end-infer-scope @ // { InferScope ?r ?u ?rho ?sig ?l [ ] ?s } -- |
{ Stack ?s ?sig }
{ Scope ?r ?u ?rho ?sig ?l } ;


! NOTE: we really need to capture f here!
CHR: step-infer-scope-1 @ { InferScope ?r ?u ?rho ?sig ?l ?p ?s } // -- [ ?p empty? not ]
[ ?p unclip-slice [ :>> ?q ] [ f <wrapper> or :>> ?w ] bi* drop ]
[ ?s seq-state :>> ?t ]
|
{ InferNext ?s ?t ?w ?q }
    ;

! CHR: link-infer-up @ { InferNext ?r ?s __ __ } // { Link ?s ?u } -- | { Link ?r ?u } ;

CHR: infer-wrapper @ // { InferNext ?s ?t ?w ?q } -- [ ?w wrapper? ] |
[| | ?w wrapped>> :> x { Push ?s ?t x } ]
{ Inferred ?s ?t ?q }
    ;

CHR: infer-push @ // { InferNext ?s ?t A{ ?w } ?q } -- [ ?w word? not ] |
{ Push ?s ?t ?w }
{ Inferred ?s ?t ?q } ;

CHR: infer-word-check-exec-1 @ // { InferNext ?s ?t ?w ?q } -- [ ?w word? ] { CheckExec ?s ?t ?w ?x } |
[ ?x known [ { RecursiveCall ?s ?t ?w ?x } ] [ { Exec ?s ?t ?w  } ] if ]
{ Inferred ?s ?t ?q }
    ;

! If execution made the scope redundant, we shouldn't enter this!
CHR: step-infer-scope-2 @ // { Inferred ?s ?t ?q } { InferScope ?r ?u ?rho ?sig ?l __ ?s } -- |
[| |
 ?l ?t suffix! :> sub
    { InferScope ?r ?u ?rho ?sig sub ?q ?t }
] ;

CHR: manual-next @ { InferScope ?r ?u ?rho ?sig ?l ?q ?s } // { InsertStates ?s ?t } -- |
[ ?t ?l push-all f ] ;

CHR: dangling-infer @ // { Inferred __ __ __ } -- | ;

! chr: start-infer @ // { InferBetween ?r ?t ?q f } -- [ ?q known? ] { Stack ?r ?rho } |
! ! { Stack ?r ?rho }
! ! { Scope ?r ?t { ?s } }
! [| | ?s 1vector :> l { InferScope ?r ?t l } ]
! { Infer ?r ?s ?q }
! { Stack ?s ?rho } ;

! CHR: modal-end-infer @ // { ask { InferBetween ?r ?t ?q } } { Infer ?r ?x [ ] } -- |
! { entailed { InferBetween ?r ?t ?q } } ;

! CHR: end-infer @ { InferBetween ?r ?t ?q ?l } // { Infer ?r ?x [ ] } -- |
! { Stack ?x ?rho } { Stack ?t ?rho } ;
! CHR: end-infer @ // { InferScope ?r ?t ?a } { ask { InferBetween ?r ?t ?q ?l } } { Infer ?r ?x [ ] } -- { Stack ?x ?sig } |
! ! { Stack ?x ?rho } { Stack ?t ?rho }
! { EndStack ?t ?sig }
! [ ?l ?a >array ==! ]
! { entailed { InferBetween ?r ?t ?q ?l } }
!     ;
! { CleanScope ?r ?t }
! { EndInferScope ?x } ;

! CHR: modal-infer-start @ { ask { InferBetween ?r ?t ?q __ } } // -- |
! { InferBetween ?r ?t ?q f } ;

! CHR: infer-step @
! { InferScope ?r ?t __ }
! //
! ! { InferBetween ?r ?t __ ?l }
! { Infer ?r ?s ?q } -- [ ?q empty? not ]
! | [| |
!    ?s seq-state :> sn
!    ?q unclip-slice :> ( rest w )
!    { InferNext ?r ?s sn w rest }
!   ] ;

! ! NOTE: We cut this into a two-step rule, because an Exec might render the whole branch invalid
! CHR: infer-next-word @ { InferNext ?r ?s ?t ?w ?q } // -- | [| |
!     ?w wrapper? [ ?w wrapped>> :> x { Push ?s ?t x } ]
!     [ { Exec ?s ?t ?w } ] if
! ] ;

! CHR: infer-next-rest @ { InferScope ?r __ ?l } // { InferNext ?r __ ?t __ ?q } -- |
!     ! { AddLink ?r ?t }
! [ ?t ?l push f ]
! { Infer ?r ?t ?q } ;

! ! Link interface
! CHR: link-infer-up @ { InferScope ?r __ ?l } // { Link ?s ?u } -- [ ?s ?l known in? ] | { Link ?r ?u } ;

;
