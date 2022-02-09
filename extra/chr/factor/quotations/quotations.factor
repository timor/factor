USING: chr chr.factor chr.factor.words chr.modular chr.parser chr.state kernel
math quotations sequences types.util ;

IN: chr.factor.quotations

! * Quotation Inference
TERM-VARS: ?p ?q ?r ?s ?t ?u ?a ?b ?c ?d ?n ?w ;

! ** Keep track of word sequencing
TUPLE: Link < chr-pred a b c ;
TUPLE: link-seq < chr-pred pred succ o ;

CHRAT: call-seq { link-seq }
! CHR{ { Word ?s ?t __ } // -- | { Link ?s ?t } }
CHR{ { Link ?s ?t ?u } // { Link ?s ?t ?u } -- | }
! CHR{ { Link ?s ?t ?t } // { Link ?s ?t ?u } -- | { Link ?s ?u ?u } }
! CHR{ { Link ?s ?s ?t } // { Link ?s ?s ?u } -- | { Link ?s ?u ?u } }
! CHR{ // { ask { link-seq ?s ?s ?s } } -- | { entailed { link-seq ?s ?s ?s } } }
CHR{ { Link ?s ?t ?t } // { ask { link-seq ?s ?t ?t } } -- | { entailed { link-seq ?s ?t ?t } } }
CHR{ { Word ?r ?s } { Word ?s ?t } // { Link ?s ?t ?t } -- | { Link ?r ?s ?s } }
    ;

! ** Low-level Stack operations

CHRAT: stack-ops { Push Pop Pops Pushes }
CHR{ { Val ?s ?n ?a } // { Val ?s ?n ?a } -- | }
CHR{ { Val ?s ?n ?a } // { Val ?s ?n ?b } -- | [ ?b ?a ==! ] }

! Sanity check
CHR{ { Val __ ?n __ } // -- [ ?n 0 < ] | [ "error" throw ] }

CHR{ // { Pops ?s ?t ?a } -- | [ ?a [ f ] [| seq | seq unclip :> ( rest e ) ?s sub-state :> s1 { { Pops s1 ?t rest } { Pop ?s s1 e } } ] if-empty ] }
CHR{ // { Pop ?s ?t { ?a ?u } } -- | { Pop ?s ?t ?a } { Instance ?a ?u } }
CHR{ // { Pop ?s ?t ?a } -- |
     { Val ?s 0 ?a }
     { ShiftPop ?s ?t 1 } }

CHR{ // { Pushes ?s ?t ?a } -- | [ ?a [ f ] [| seq | seq unclip :> ( rest e ) ?s sub-state :> s1 { { Pushes s1 ?t rest } { Push ?s s1 e } } ] if-empty ] }
CHR{ // { Push ?s ?t { ?a ?u } } -- | { Push ?s ?t ?a } { Instance ?a ?u } }
CHR{ // { Push ?s ?t ?b } -- |
     { Val ?t 0 ?b }
     { ShiftPush ?s ?t 1 }
   }

! ShiftPop
! ---↗  /------
! -----/ ↗-----
! ! Request from left
CHR{ { ShiftPop ?s ?t ?d } { Val ?s ?n ?a } // -- [ ?n ?d >= ] |
     [| | ?n ?d - :> l
      { Val ?t l ?a }
     ]
   }
! ! Request from right
CHR{ { ShiftPop ?s ?t ?d } { Val ?t ?n ?a } // -- |
     [| | ?n ?d + :> l
      { Val ?s l ?a }
     ]
   }
! ShiftPush
! ----\  ↘------
! ---↘ \--------
! ! Request from left
CHR{ { ShiftPush ?s ?t ?d } { Val ?s ?n ?a } // -- |
     [| | ?n ?d + :> l { Val ?t l ?a } ]
   }
! ! Request from right
CHR{ { ShiftPush ?s ?t ?d } { Val ?t ?n ?a } // -- [ ?n ?d >= ] |
     [| | ?n ?d - :> l { Val ?s l ?a } ]
   }

! Transitivity
! CHR{ // { ShiftPop ?s ?t ?d } { ShiftPop ?t ?u ?e } -- |
!      [| | ?d ?e + :> l { ShiftPop ?s ?u l } ]
!    }
! CHR{ // { ShiftPush ?s ?t ?d } { ShiftPush ?t ?u ?e } -- |
!      [| | ?d ?e + :> l { ShiftPush ?s ?u l } ]
!    }

    ;

! ** Translation
TERM-VARS: ?beg ;
TUPLE: StartInfer < chr-pred s quot ;
TUPLE: EndInfer < chr-pred beg end ;
TUPLE: Infer < chr-pred beg s quot ;
TUPLE: InferFresh < chr-pred quot ;

CHRAT: infer-stack { StartInfer InferFresh }
IMPORT: stack-ops
CHR{ { InferUnknown __ __ ?q } // -- | { Instance ?q callable } }
CHR{ { BranchIf __ __ ?c __ __ } // -- | { Instance ?c boolean } }
CHR{ // { Infer ?beg ?s [ ] } -- | { EndInfer ?beg ?s } }
CHR{ // { Infer ?beg ?s ?q } -- | [| | ?q unclip :> ( rest w ) ?s seq-state :> sn { { Word ?s sn w } { Infer ?beg sn rest } } ] }
CHR{ { StartInfer ?s ?q } // -- | [| | ?s sub-state :> si { Infer ?s si ?q } ] }
CHR{ // { InferFresh ?q } -- | [ state-in ?q StartInfer boa ] }
CHR{ { Word ?s ?t ?w } // -- | [ ?s ?t ?w tell-chr ] }
;

! * Interface
: chrat-infer ( quot -- constraints )
    '{ { InferFresh _ } } run-chrat-query ;
