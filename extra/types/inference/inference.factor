USING: accessors arrays combinators.short-circuit continuations effects inverse
kernel kernel.private make math namespaces persistent.vectors quotations
sequences sets types.expander types.type-values types.util words ;

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

! TODO: add cached types here
: in-types ( word -- seq )
    { [ "input-classes" word-prop? ]
      [ dup word? [ stack-effect in>> length object <repetition> ] [ drop f ] if ]
    } 1|| ;
    ! dup { [ primitive? ] [ "input-classes" word-prop ] }
    ! [ "input-classes" word ]
    ! dup word?
    ! [ stack-effect effect-in-types ]
    ! [ drop f ] if ;

: out-types ( word -- n )
    { [ "default-output-classes" word-prop? ]
      [ dup word? [ stack-effect out>> length object <repetition>
                  ] [ <wrapper> 1array ] if ]
    } 1|| ;
    ! dup word?
    ! [ stack-effect effect-out-types ]
    ! [ <wrapper> 1array ] if ;

: make-enough ( stack in-decls -- stack )
    dupd ?shorter
    [ [ <??> ] replicate prepend ] when* ;

: constrain-inputs ( stack word -- stack )
    in-types
    [ make-enough ]
    [ apply-declaration ] bi ;

SYMBOLS: quot-done quot-todo ;

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
    [ <configuration> unadd-word { } ]
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

: perform-word ( stack word -- stack )
    do-word ;
    ! dupd do-word with-datastack ;
    ! 2dup type-expand
    ! [  ]
    ! [ do-word ] if* ;

: apply-word ( stack word -- stack )
    [ apply-inputs ] keep swap
    [ perform-word ] [ drop ] if ;
    ! [ perform-word ] bi ;

: (apply-quotation) ( stack quot -- stack )
    quot-todo set
    [ ] quot-done set
    forward
    <configuration> add-word { }
    ;

: apply-quotation ( stack quot -- stack )
    [ (apply-quotation) ] with-scope ;

M: object undo-word
    out-types
    [ apply-declaration
      dup divergent-stack? [ divergent-undo ] when ]
    [ length head* ] bi ;

! Inputs have been constrained already

: n-in ( x -- x )
    in-types length ;

M: object do-word
    [ >value suffix ]
    [ add-word ] bi ;
    ! [ n-in head* ]
    ! [ out-types [ decl>value suffix ] each ]
    ! [ add-word ] tri ;

! : maybe-fold ( stack word -- stack )
!     dupd [ n-in macro-literals ] keep swap
!     [  ]

: pop-macro-inputs ( stack n -- stack seq/f )
    2dup macro-literals
    [ [ head* ] dip ]
    [ 2drop f ] if ;

SYMBOL: word-stack
: fold? ( word -- ? )
    { [ foldable? ]
      [ "shuffle" word-prop? ]
    } 1|| ;

! :: ?fold-word ( stack word -- stack ? )
!     word fold?
!     [ word n-in :> n
!       stack n pop-macro-inputs :> ( stack inputs )
!       inputs
!       [ word 1quotation with-datastack
!         n cut-words
!         [ literalize add-word ] each
!       ]
!       [ stack f ] if*
!     ]
!     [ stack f ] if ;
!     ! dup fold?
!     ! [ [ n-in pop-macro-inputs ] keep swap
!     !   [ swap 1quotation with-datastack
!     !     [ literalize add-word ] each
!     !     t ]
!     !   [ drop f ] if* ]
!     ! [ drop f ] if ;

! TODO: do we keep the configuration in the code?
: do-inputs ( stack effect -- stack )
    in>> length cut* <configuration> add-word ;

: do-outputs ( stack effect -- stack )
    effect-out-types [ decl>value ] map append ;

: do-static-effect ( stack word -- stack )
    dup stack-effect
    [ nip do-inputs ]
    [ drop add-word ]
    [ nip do-outputs ] 2tri ;

M: word do-word
    ! dup word-stack get in? [ "recursive" 2array throw ] when
    ! word-stack get over suffix word-stack [
        do-static-effect
    ;
    ! ] with-variable ;
    ! [ ?fold-word ] keep swap
    ! [ drop ]
    ! [
    !       word-stack get over suffix word-stack
    !       [ def>> apply-quotation ] with-variable
    ! ] if ;

! Invariant undo: If we could have produced the outputs, assume we did.
! Annotation is not done on the way back
ERROR: incompatible-outputs ;
: undo-outputs ( stack effect -- stack )
    [ effect-out-types [ decl>value ] map stacks-intersect? ] 2keep rot
    [ out>> length head* ]
    [ incompatible-outputs ] if ;

! Invariant undo: push unknown inputs.  Any declaration to refine this should
! have been present in the forward direction
: undo-inputs ( stack effect -- stack )
    effect-in-types [ decl>value ] map append ;

: undo-static-effect ( stack word -- stack )
    dup stack-effect
    [ nip undo-outputs ]
    [ drop unadd-word ]
    [ nip undo-inputs ] 2tri ;


! M: word undo-word "undefined undo" 2array throw ;
M: word undo-word
    undo-static-effect ;
    ! "undefined undo" 2array throw ;


: do-immediate ( stack word -- stack )
    1quotation with-datastack ;

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

    ! elements>> intersect-type-values
    ! [ elements>> stacks-intersect? ] keep swap
    ! [ length head* ]
    ! [ quot-done get quot-todo get configuration-mismatch ] if ;


! Interface

: magic ( quot -- quot )
    [ { } swap (apply-quotation) quot-done get ] with-scope nip ;

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

! * Type configuration annotation
