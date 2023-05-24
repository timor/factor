USING: accessors arrays assocs assocs.extras chr.factor chr.parser classes
classes.algebra classes.algebra.private classes.union combinators.short-circuit
combinators.smart generic.math generic.single kernel make math namespaces
quotations sequences sets terms types.util words ;

IN: chr.factor.util

! ** Stacks

: known-compatible-stacks? ( l1 l2 -- ? )
    { [ [ llength* ] same? ]
        [ [ lastcdr ] same? ] } 2&& ;

! ** Effect Type Isomorphism
GENERIC: expand-xor ( xor -- seq )
M: Xor expand-xor [ type1>> ] [ type2>> ] bi
    [ expand-xor ] bi@ append ;
M: object expand-xor 1array ;

GENERIC: effect>nterm ( effect -- term )
M: Xor effect>nterm
    expand-xor
    [ effect>nterm ] map <match-set> ;

M: object effect>nterm ;

M: Instance effect>nterm
    clone [ effect>nterm ] change-type ;

M: Effect effect>nterm
    {
        [ in>> ]
        [ out>> ]
        [ preds>>
          [ effect>nterm ] map <match-set>
        ]
        [ parms>> <match-set> ]
    } cleave>array ;

! The tag is unimportant for comparison
M: Iterated effect>nterm
    clone [ drop __ ] change-tag ;

: same-effect? ( e1 e2 -- ? )
    [ effect>nterm ] bi@ isomorphic? ;

! ** Recursion
PREDICATE: effect-instance < Instance type>> valid-effect-type? ;

: has-recursive-call? ( tag Effect -- ? )
    preds>> [ dup CallRecursive? [ tag>> = ] [ 2drop f ] if ] with any? ;

! FIXME unused
: filter-recursive-call ( tag Effect -- Effect )
    clone
    [ [ dup CallRecursive? [ tag>> = ] [ 2drop f ] if ] with reject ] with change-preds ;

GENERIC#: recursive-branches? 1 ( type word/quot -- ? )
M: Effect recursive-branches? swap has-recursive-call? ;
M: Xor recursive-branches? [ [ type1>> ] [ type2>> ] bi ] dip '[ _ recursive-branches? ] either? ;
GENERIC#: terminating-branches 1 ( type word/quot -- branches )
M: Effect terminating-branches over has-recursive-call? [ drop f ] [ 1array ] if ;
M: Xor terminating-branches [ [ type1>> ] [ type2>> ] bi ] dip '[ _ terminating-branches ] bi@ append sift ;
GENERIC#: recursive-branches 1 ( type word/quot -- branches )
M: Effect recursive-branches over has-recursive-call? [ 1array ] [ drop f ] if ;
M: Xor recursive-branches [ [ type1>> ] [ type2>> ] bi ] dip '[ _ recursive-branches ] bi@ append sift ;

GENERIC: substitute-recursive-call ( orig replacement obj -- obj )
M: object substitute-recursive-call 2nip ;
M:: Xor substitute-recursive-call ( from to obj -- obj )
    from to obj type1>> substitute-recursive-call
    from to obj type2>> substitute-recursive-call Xor boa ;
M: Effect substitute-recursive-call
    clone [ [ substitute-recursive-call ] 2with map ] change-preds ;
! NOTE: excluding effect instances here for now!
! NOTE: including it though!
M: effect-instance substitute-recursive-call
    clone [ substitute-recursive-call ] change-type ;
! FIXME: this would be much easier with a subtree-matcher!
GENERIC: replace-call-recursive ( in out new -- res )
M: \ null replace-call-recursive 3drop P{ Invalid } ;
M:: valid-effect-type replace-call-recursive ( in out new -- res )
    P{ ApplyEffect new in out } ;

:: call-recursive-substitute-recursive-call ( obj to -- obj )
    obj P{ CallRecursive __ ?a ?b } solve-eq
    ! [ solve-eq ] no-var-restrictions
    [ ?a of ] [ ?b of ] bi to replace-call-recursive ;

M:: CallRecursive substitute-recursive-call ( from to obj -- obj )
    obj tag>> from = [ obj to call-recursive-substitute-recursive-call ] [ obj ] if ;

! ** Class algebra

: pessimistic-math-class-max ( class class -- class )
    math-class-max dup { fixnum bignum } in? [ drop integer ] when ;

! TODO: make this better!
: bounded-class? ( class? -- ? )
    { [ object eq? ]
      ! [ mixin-class? ]
      [ union-class? ]
      [ anonymous-union? ]
      [ anonymous-complement? ]
    } 1|| not ;

! ** Generic Dispatch

! XXX Compleeeeeeeeeeeeeeetely unsure about this right now...
: applicable-methods ( class methods -- methods )
    [ classes-intersect? ] with filter-keys ;
    ! [ swap class<= ] with filter-keys ;

! Call site is constrained if the set of methods (excluding the default method) after
! checking the class intersection is a proper subset?
! TODO maybe make a difference if the class is a union or mixin?
! Different strategy: If it's directly in there and not the default method, then
! go for it.  Otherwise, if it's a union class or mixin, then not.
! Too general.  Restricting to bounded classes only for now
: constrains-methods? ( class methods -- ? )
    {
        ! [ [ default-method? ] reject-values key? ]
        [ drop bounded-class? ] } 2|| ;

: constrain-methods ( class methods -- methods/f )
    2dup constrains-methods?
    [ applicable-methods ] [ 2drop f ] if ;

! This is actually the one spot where we can declare that things don't overlap
! although they would do if we inferred them as random possible branches of an
! XOR type.  Normally, if parameters overlap, we unionize them to enforce
! XOR-Property, i.e. ensure that actually only one branch can be taken.  Here we
! explicitly encode the not-instance declarations which would be implied during
! runtime dispatch.
! Takes an ordered list of { class method } specs, and modifies it to exclude
! previous ones.
: make-disjoint-classes-step ( not-class next-in -- not-class next-out )
    [ swap class-not simplifying-class-and ]
    [ class-or ] 2bi swap ;

: make-disjoint-classes ( classes -- classes )
    null swap [ make-disjoint-classes-step ] map nip ;

! NOTE: not doing the explicit exclusions when inferring from if-instance cascades
: enforce-dispatch-order ( methods -- methods )
    <reversed> ;
    ! <reversed> unzip [ make-disjoint-classes ] dip
    ! zip ;

: dispatch-method-seq ( single-generic -- seq )
    dup "methods" word-prop sort-methods object over key?
    [ nip ]
    [
        [ "default-method" word-prop object swap 2array ] dip swap prefix
    ] if enforce-dispatch-order ;

: dispatch-decl ( class num -- seq )
    ! dup 1 + object <array> [ set-nth ] keep ;
    object <array> swap prefix ;

! NOTE: that 1quotation there causes the method to actually be a word inside
! the quotation.  A simple [ M\ foo bar ] entered literally would result in a quotation
! pushing the wrapped method on the stack!
: dispatch-method-case ( picker method -- quot )
    first2 ! ( picker class method )
    [ 1quotation [ instance? ] compose compose ] dip
    1quotation 1quotation compose ;

! Whish they didn't do this as hook combination...
: picker* ( generic -- quot )
    "combination" word-prop combination [ picker ] with-variable ;

: dispatcher-quot ( generic methods -- quot )
    dup length 1 >
    [ unclip
      [ over picker* ] dip dispatch-method-case
      [ dispatcher-quot ] dip
      swap '[ @ _ if ]
    ] [ nip first second 1quotation ] if ;

! ** Completeness

! ! NOTE: doesn't check in instances!
! GENERIC: unresolved-recursive? ( allowed type -- ? )
! M: Effect unresolved-recursive?
!     preds>> [ unresolved-recursive? ] with map-find drop ;
! M: object unresolved-recursive? 2drop f ;
! M: CallRecursive unresolved-recursive? tag>>
!     2dup = [ 2drop f ] [ nip ] if ;
! M: CallXorEffect unresolved-recursive?
!     "should not be checked in this form!" throw ;
! M: Xor unresolved-recursive?
!     { [ type1>> unresolved-recursive? ]
!       [ type2>> unresolved-recursive? ]
!     } 2|| ;

GENERIC: recursive-tags* ( x -- )
M: object recursive-tags* drop ;
M: Effect recursive-tags* preds>> [ recursive-tags* ] each ;
M: Xor recursive-tags*
    [ type1>> recursive-tags* ] [ type2>> recursive-tags* ] bi ;
M: CallRecursive recursive-tags* tag>> , ;
M: Instance recursive-tags* type>> recursive-tags* ;
M: CallXorEffect recursive-tags* "Don't look for unresolved effect recursives!" throw ;
M: ApplyEffect recursive-tags* effect>> recursive-tags* ;

: recursive-tags ( obj -- seq )
    [ recursive-tags* ] { } make members [ f ] when-empty ;

: singly-recursive? ( word type -- ? )
    [ 1array ] [ recursive-tags ] bi* set= ;

GENERIC: canonical? ( x -- ? )
M: term-var canonical? drop f ;
M: Effect canonical? preds>> [ canonical? ] all? ;
M: body-pred canonical? drop t ;
M: CallRecursive canonical? drop f ;
M: Xor canonical?
    [ type1>> ] [ type2>> ] bi [ canonical? ] both? ;
M: CallXorEffect canonical? "xor calls should be resolved here" throw ;
M: effect-instance canonical? type>> canonical? ;
    ! Those are not body preds, but used when prepping
M: ApplyEffect canonical? effect>> canonical? ;
M: Invalid canonical? drop t ;
M: Ensure canonical? drop t ;

! ** Xor Calls

GENERIC: xor-call? ( type -- ? )
M: Effect xor-call? preds>> [ CallXorEffect? ] any? ;
M: Xor xor-call? [ type1>> ] [ type2>> ] bi [ xor-call? ] bi@ or ;

! find object satisfying quot, if found, return with rest of sequence.  Otherwise
! return sequence unchanged and f.
: find-remove ( seq quot -- seq obj/f )
    dupd find
    [ [ swap remove-nth ] dip ] when* ; inline

:: split-xor-call-preds ( preds -- then-preds else-preds )
    preds [ CallXorEffect? ] find-remove swap :> rest-preds
    [ in>> ] [ out>> ] [ type>> ] tri
    [ type1>> ] [ type2>> ] bi
    :> ( call-in call-out then-type else-type )
    rest-preds P{ ApplyEffect then-type call-in call-out } suffix
    rest-preds P{ ApplyEffect else-type call-in call-out } suffix ;

:: split-xor-call-effect ( effect inst-var -- then-effect else-effect )
    effect preds>> [ CallXorEffect? ] find-remove
    [ in>> ] [ out>> ] [ type>> ] tri
    [ type1>> ] [ type2>> ] bi
    :> ( rest-preds call-in call-out then-type else-type )
    effect [ in>> ] [ out>> ] [ parms>> ] tri
    rest-preds P{ CallEffect inst-var call-in call-out } suffix Effect boa
    dup clone
    [ [ P{ Instance inst-var then-type } suffix ] change-preds ]
    [ [ P{ Instance inst-var else-type } suffix ] change-preds ] bi* ;

! ** Liveness scoping
: value-vars ( stack -- vars )
    list>array* members ;

: stack-vars ( stack -- vars row )
    list*>array unclip-last ;
