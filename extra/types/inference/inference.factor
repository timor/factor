USING: accessors arrays combinators combinators.short-circuit continuations
effects inverse kernel kernel.private make math namespaces persistent.vectors
quotations sequences types types.expander types.type-values types.typed-calls
types.util words ;

IN: types.inference

FROM: namespaces => set ;
! * Call a word in type context
! : type-call

! * Code Walker, building transfers as we go

! Looks at the code as we go, tries to convert in into a type-level quotation.

TUPLE: typestack
    id types ;
: <empty-stack> ( -- obj )
    \ typestack counter
    PV{ } typestack boa ;

SYMBOL: current-type-stack
SYMBOL: word-accum
SYMBOL: rest-code
GENERIC: type-transfer ( word -- transfer )

: fold-+ ( a b -- a b quot )
{
    { [ { fixnum fixnum } declare ]
      [ 2dup + 1quotation [ drop drop ] prepose ] }
    { [ { fixnum } declare ]
      [ dup [ + ] curry [ drop ] prepose ] }
    { [ { fixnum object } declare ]
      [ over '[ nip _ + ] ] }
    { [ ] [ [ + ] ] }
} switch ;

: fold-call ( callable -- quot )
    {
        { [ { callable } declare ]
          [  ] }
        { [  ] [ [ call ] curry ] }
    } switch ;

! * Control flow focus
! Ok so in the end everything is about control flow.  Types are about dispatch,
! and dispatch is about control flow.  So what we actually normally want to do
! is run straight-line code.  If we can't do that, but we have different
! possibilities, then we can construct a conditional expression instead.

! * Predicate language/Partial evaluation
! Language of things that can be used to restrict possibilities at compile time
! If we assume pattern-matching dispatch at runtime, we need the dual
! functionality of pattern match at compile time, which will predict whether a
! predicate can dispatch.

! Semantically speaking, we want to perform a computation.  The only reason to
! not be able to do fold this immediately is if we don't have enough information.  So
! we need to assume this information.  At that instant, you could think of the
! evaluator throwing back to the environment, saying I can't do that.

! We could ask a different instance why we weren't able to do that, or under
! what conditions we would be able to do that.

! Then the environment could ask an approximating evaluator to provide a piece of code
! instead.  So the result of a partial evaluation is actually a piece of code to
! call instead.

! By that definition, every word that does not have enough information about the
! inputs will have to replace itself by something that can be run instead.

! Any computations that are performed during compilations need to have a defined
! inverse to ensure that matching succeeds.  If it does not, unification would
! not be possible.  So if a match does not succeed on one partner, we can ask a
! different partner to advance instead?

SYMBOL: folded?
: fold-word? ( stack word -- ? )
    { [ nip foldable? ] [ enough? ] } 2&& ;

: apply-fold ( stack word -- stack )
    2dup { [ nip word? not ] [ fold-word? ] } 2||
    [ 1quotation with-datastack folded? on ]
    [ [ [ literalize , ] each ] [ , ] bi* { } ]
    if ;

: maybe-fold ( quot -- folded-quot )
    [ { } [ apply-fold ] reduce % ] [ ] make ;

: add-fold-word ( quot word -- quot )
    suffix maybe-fold flatten ;

: fold/flatten ( quot -- expanded )
    f folded? [
        ! expand-macros
        [ ] [ add-fold-word ] reduce
        folded? get
        [ fold/flatten ] when
    ] with-variable ;

: [tundo] ( quot -- undo )
    fold/flatten reverse [ (undo) ] [ ] make ;

! : fold/flatten ( quot -- expanded )
!     visited get over suffix visited [
!         [
!             dup flattenable? [
!                 def>>
!                 [ visited get member-eq? [ no-recursive-inverse ] when ]
!                 [ fold/flatten ]
!                 bi
!             ] [ 1quotation ] if
!         ] map concat
!     ] with-variable ;


! Translations:

! * Transformation
! Folding works by running words on a value stack
! 1. If we can execute the word to map values to values, do so
! 2. If not, take all accumulated values, turn them into literals and add them
! and the word to the quotation

! This is an operation where we try to substitute a word with an equivalent word
! that works from the empty stack.  This is an extreme form of peephole
! optimization.

! The partial evaluation equivalent would be different: If we cannot fold the
! word, we perform a substitution calculation instead.  We do that by executing
! an equivalent definition that works on value sets instead of values, carrying
! information about what properties the value must have if it had run.  This
! information is represented as a set of constraints/propositions/properties
! that are subtracted from the unknown domain


! ** Folding/Macros/Inlining
! Folding means that we can actually perform a structural reduction on the
! quotation based on the word that comes next.
! This is the simplest way of partial evaluation
! 1. Run the program word by word.
! 2. If the word has enough inputs, run it
!    If the word does not have enough inputs, literalize all the values we have,
!    add them and the quotation to the quotation accumulator.


TUPLE: input id ;
: <input> ( -- val ) input counter input boa ;

: make-enough ( stack in-decls -- stack )
    dupd ?shorter
    [ [ <??> ] replicate prepend ] when* ;

: constrain-inputs ( stack word -- stack )
    in-classes
    [ make-enough ]
    [ apply-declaration ] bi ;

SYMBOLS: quot-done quot-todo stack-in ;

: cut-words ( n -- )
    quot-done [ swap head* ] change ;

: add-word ( word -- )
    quot-done [ swap suffix ] change ;

: unadd-word ( word -- )
    quot-todo [ swap prefix ] change ;

ERROR: divergent-undo ;
GENERIC: undo-word ( stack word -- stack )
DEFER: apply-inputs
! : rewind-word ( stack word -- stack )
!     ! dupd undo-word with-datastack ;
!     [ undo-word ] keep
!     apply-inputs [ re ]
!     ;

! : rewind ( stack -- stack )
!     quot-done get
!     [ unclip-last swap quot-done namespaces:set
!       rewind-word
!     ] unless-empty ;

: rewind ( stack -- stack )
    quot-done get
    [ dup stack-in set ]
    [ unclip-last swap quot-done namespaces:set
      [ undo-word ]
      [ constrain-inputs ] bi
      rewind
    ] if-empty ;

DEFER: apply-word
: forward ( stack -- stack )
    quot-todo get
    ! [ <configuration> add-word { } ]
    [ unclip swap quot-todo set
      apply-word forward
    ! ] if-empty ;
    ] unless-empty ;


! : apply-inputs ( stack word -- stack valid? )
!     [ constrain-inputs ] keepd over =
!     [ t ]
!     [ rewind forward f ] if ;
:: apply-inputs ( stack word -- stack continue? )
    stack word constrain-inputs :> new-stack
    stack new-stack =
    [ stack t ]
    [ word unadd-word
      new-stack rewind forward f ] if ;

GENERIC: do-word ( stack word -- stack )

DEFER: apply-quotation

: fold? ( word -- ? )
    dup word?
    [ { [ foldable? ]
      [ "shuffle" word-prop? ]
      } 1|| ]
    [ drop f ] if ;

: literal? ( obj -- ? )
    { [ word? not ]
      [ type-call? not ]
      [ configuration? not ]
    } 1&& ;

: ?cut* ( seq n -- seq1 seq2/f )
    over length over >=
    [ cut* ]
    [ drop f ] if ;

: n-in ( x -- x )
    in-classes length ;

: fold-literals ( word -- seq/f )
    dup fold?
    [ n-in quot-done get swap ?cut*
      [
          dup [ literal? ] all?
          [ swap quot-done set ]
          [ 2drop f ] if
      ] [ drop f ] if* ]
    [ drop f ] if
    ;

: kill-literals ( stack seq/f -- stack )
    length head* ;

: ?fold-word ( stack word -- stack quot/f )
    dup fold-literals
    [
        [ nip kill-literals ]
        [ swap 1quotation with-datastack [ literalize ] [ ] map-as ]
        2bi
    ]
    [ drop f ] if* ;

: ?transform-word ( stack word -- stack quot/f )
    { [ ?fold-word ]
      [ dupd type-expand ]
    } 1||
    ;

DEFER: (apply-quotation)
: perform-word ( stack word -- stack )
    [ ?transform-word ] keep swap
    [ nip (apply-quotation) ]
    [ do-word ] if* ;

    ! do-word ;
    ! dupd do-word with-datastack ;
    ! 2dup type-expand
    ! [  ]
    ! [ do-word ] if* ;

: apply-word ( stack word -- stack )
    [ apply-inputs ] keep swap
    [ perform-word ] [ drop ] if ;
    ! [ perform-word ] bi ;

: (apply-quotation) ( stack quot -- stack )
    quot-todo [ compose ] change
    forward ;
    ! dup empty? [ stack-out set { } ] unless ;

: stacks>effect ( in-stack out-stack -- effect )
    [ [ f swap 2array ] map { } or ] bi@ <effect> ;

: apply-quotation ( stack quot -- typed-call )
    [
        [ ] quot-todo set
        [ ] quot-done set
        stack-in off
        (apply-quotation)
        stack-in get swap
        stacks>effect
        quot-done get
        <type-call>
    ] with-scope ;

M: object undo-word
    dup unadd-word
    out-classes
    [ apply-declaration
      dup divergent-stack? [ divergent-undo ] when ]
    [ length head* ] bi ;

: do-value ( stack word -- stack )
    [ >value suffix ]
    [ add-word ] bi ;

M: object do-word
    do-value ;

M: wrapper do-word
    wrapped>> do-value ;

: pop-macro-inputs ( stack n -- stack seq/f )
    2dup macro-literals
    [ [ head* ] dip ]
    [ 2drop f ] if ;

SYMBOL: word-stack
: do-inputs ( stack effect -- stack types )
    ! in>> length cut* <configuration> add-word ;
    in>> length cut* ;

: do-outputs ( stack word -- stack types )
    out-classes [ decl>value ] map [ append ] keep ;

:: do-static-effect ( stack word -- stack )
    word stack-effect :> e
    stack e do-inputs :> ( stack in-types )
    stack word do-outputs :> ( stack out-types )
    in-types out-types stacks>effect word 1quotation <type-call> add-word
    stack ;
    ! dup stack-effect
    ! [ nip do-inputs ]
    ! [ drop add-word ]
    ! [ nip do-outputs ] 2tri
    ! ;

: do-immediate ( stack word -- stack )
    1quotation with-datastack ;

M: word do-word
    { { [ dup "shuffle" word-prop ] [ dup add-word do-immediate ] }
      [ do-static-effect  ]
    } cond ;

! Invariant undo: If we could have produced the outputs, assume we did.
! Annotation is not done on the way back
ERROR: incompatible-outputs stack types ;

: undo-type-outputs ( stack types -- stack )
    2dup stacks-intersect?
    [ length head* ]
    [ incompatible-outputs ] if ;

! : undo-effect-outputs ( stack effect -- stack )
!     [ effect-out-types [ decl>value ] map stacks-intersect? ] 2keep rot
!     [ out>> length head* ]
!     [ incompatible-outputs ] if ;

! ! Invariant undo: push unknown inputs.  Any declaration to refine this should
! ! have been present in the forward direction
! : undo-effect-inputs ( stack effect -- stack )
!     effect-in-types [ decl>value ] map append ;

! : undo-static-effect ( stack word -- stack )
!     dup stack-effect
!     [ nip undo-effect-outputs ]
!     [ drop unadd-word ]
!     [ nip undo-effect-inputs ] 2tri ;

: spec>types ( seq -- seq )
    [ dup pair? [ second ] when ] map ;

M: static-type-call undo-word ( stack word -- stack )
    [ type-spec>> out>> spec>types undo-type-outputs ]
    [ quot>> quot-todo [ compose ] change ]
    [ type-spec>> in>> spec>types append ] tri ;


M: word undo-word "undefined undo" 2array throw ;
! M: word undo-word
!     undo-static-effect ;

M: \ swap do-word
    dup add-word do-immediate ;

M: \ swap undo-word
    dup unadd-word do-immediate ;

ERROR: configuration-mismatch bad-stack stack configuration lhs rhs ;
: apply-configuration ( stack configuration -- stack )
    [ elements>> intersect-type-stack ] 2keep
    pick divergent-stack?
    [ quot-done get quot-todo get configuration-mismatch ]
    [ 2drop ] if ;

M: configuration do-word
    ! Keep the first configuration
    quot-done get empty? [ dup add-word ] when
    apply-configuration ;

M: configuration undo-word
    apply-configuration ;

! * Abstracting the operations
! Folding: works each word from left to right, putting literals on the stack,
! and when encountering words, trying to apply it to the literals on the stack
! by running it with with-datastack.
! If this was successful, push the resulting values onto the stack.  If not,
! un-interpret the literals, add them to the quotation, also append the word to
! the quotation.  Treat any objects remaining on the stack as literals,
! i.e. append them to the quotation

! Flattening: Visits a quotation.  For each word, fetch an equivalent definition
! and replace it with that, i.e. if the word is not flattenable, don't do
! anything.  Otherwise, replace it by its def>>.

! Macro expansion: similar to folding.  Work through each word from left to
! right.  Keeps a stack in context, and a quotation to build using make.
! If a macro is encountered, run it with datastack.  If that was successful,
! pop the last element off the stack as quotation, and expand on this instead.

! Note that the expander code is not run in the stack checker.  That one has its
! own implementation along with the transform-quot mechanism.

! The stack checker does all of these in parallel

! So the overall pattern:
! 1. Initialize an empty stack, and a quotation to build
! 2. For each word
!    1. Is there an equivalent definition?
!       - If yes, compute it, recurse
!    2. If no, is it foldable?
!       - If yes, try to compute it on the current stack.
!    3. Otherwise, literalize the current stack, append it to the quotation.  Also
!         append the word itself to the quotation.


! There can be different reasons for the equivalent definition:

! 1. The word is inline
! 2. The word is a macro


! An inline word is basically an unconditional macro, so to speak

! These operations can be generalized into the following generics:
! : expansion ( stack word -- stack code/f)
! : stack-application ( stack word -- stack )
! : literalization ( quot value -- quot )


! ** Applying the pattern to types

! Nothing much changes, except that we keep types on the stack instead of literal
! values.  This enforces that we basically always want to have a foldable
! computation.  If it is not foldable, then we add a
! ~\ word ( ..in -- ..out ) execute-effect~ statement instead.  If, on
! reversal, we see an execute-effect statement, we have enough information to
! reverse the operation.

! A difference is folding.  Since we keep our stack in parallel, folding without
! code modification is only possible if the words are in the /exact/ same order
! on the stack.  This actually really removes the word from the code, along with
! the corresponding inputs on the stack

! It is still possible to do this on the type stack, though.  We would simply
! not add any stack literals to the quotation until we hit a non-foldable call.

! The corresponding algorithm:
! State: typestack, todo-quot, done-quot
! 1. For each word in todo-quot:
!    - Apply the word inputs to the current stack.  If they changed, rewind
!    - Otherwise
!      1. If the word is an object, push its type, add it to done-quot
!      2. Try folding:
!         - If the word is foldable
!           - Try to take the literals from done-quot, removing them, drop corresponding elements
!             from the type stack
!           - Run the word on the literals, quotationize, recurse
!      3. Else if the word has a transformation
!         - Try to take the literals from done-quot, not removing them
!         - Compute the equivalent definition, prepend droppers, recurse
!         - This includes inline words
!      4. Else if the word has a type-based transformation
!         - Same thing as above
!      5. Otherwise
!         - Compute a typed word call, append it to the quotation


! * Type transfers
! Operations that are applied to the type stack.  For static primitive words,
! this amounts to caching a configuration that is inserted

! : add-types ( quotation -- quotation )
!     [ >type-call ] map ;

! * Interface

: magic ( quot -- quot )
    [ { } swap apply-quotation ] with-scope ;
