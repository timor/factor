USING: accessors arrays continuations effects kernel macros math namespaces
quotations sequences types.algebraic words ;

IN: types.typestack

! * Inference and Macro expansion using type stacks

! Algorithm:
! State:
! - typestack, ordered sequence of types
! - pair(undo-quotation, rest-of-quotation)
! - Initially, typestack and undo-quotation are empty
! Input: quotation
! Output: fully typed trace

! Initialize rest of quotation with input quotation

! For each word in rest of quotation, from left to right:
! - If the word has a type-macro expansion
!   - apply type macro expansion to the typestack and rest of quotation
! - If the word is inline: prepend word body to rest of quotation
! - If the word is a constant
!   - remove constant from the rest of quotation onto the type stack
!   - push [ drop ] onto undo stack (possibly with type check?)
! - If the word is a regular word
!   - remove the word from the rest of the quotation
!   - take the number of required inputs from the typestack, augmenting with default
!     types if not enough
!   - push the output types onto the type stack
!   - calculate an undo quotation and append it to current undo-quotation
! - If the word is a conditional
!   - Make a copy of the trace and current typestack, then do these things:
!     - true pass
!       - replace the boolean value on the typestack with ~t~
!       - set the rest of quotation to the the true quotation
!       - Use this (output-) typestack and the trace to perform undo calculation
!       - Re-propagate forward
!     - false pass
!       - perform the same computation as above but replace the boolean with ~f~ instead
!   - After running both passes, unify the typestacks using type union


! Undo calculation:

! Same as forward calculation, but swap undo-quotation and rest-of-quotation

! Re-propagation
! State:
! - output-typestack
! - Rest of quotation
! Input:
! - input-typestack
! - trace
! Output: fully typed trace

! 1. Take all words from the trace, and form new quotation.
! 2. Perform forward pass

! ** Typestack handling

! Non-destructive
: push-type ( typestack type -- stack )
    suffix ;

: push-types ( typestack types -- stack )
    append ;

: peek-types ( typestack n -- types )
    tail ;

: pop-types ( typestack n -- typestack types )
    cut* ;

! Pop with defaults
: ?pop-types ( typestack types -- typestack types )
    2dup shorter?
    [ 2dup [ length ] bi@ swap - head swap append { } swap ]
    [ length pop-types ] if ;

! ** Iteration data structure
TUPLE: call-record inputs word ;
C: <call-record> call-record
ERROR: saving-macro-call typestack word ;


: make-call-record ( input-types word -- record )
    dup macro? [ saving-macro-call ] when
    [ stack-effect in>> length peek-types ]
    keep <call-record> ;


: save-call ( trace typestack word -- trace )
    make-call-record suffix ;

: save-literal-record ( trace typestack word -- trace )
    nip f <call-record> suffix ;

GENERIC: execute-type ( trace typestack word -- trace typestack )
M: object execute-type
    [ type-of push-type ]
    [ save-literal-record ] bi ;

! Returns the intersected types, but removes them from the typestack for the
! word to push its output types after that
: pop-input-types ( typestack word -- typestack types )
    stack-effect effect-in-types
    [ ?pop-types ]
    [ [ intersect-types ] 2map ] bi ;

: push-output-types ( typestack record  )

M: word execute-type
    [ ensure-in-effect-types ]
    [ save-call ] bi ;
    [ effect-in-types assert-in-effect-types ]
    [ in>> length pop-types ]
    [ effect-out-types swap [ +0+? ] any? [ length +0+ <array> ] when push-types ] tri
    ;

SYMBOL: word-trace
! TODO: find fixpoint
ERROR: recursive-inference word ;
! M: word execute-type
!     dup word-trace get member? [ recursive-inference ]
!     [
!         [ word-trace get  ]
!         def>> ] [ execute-type ] each ;

! Primitive base
M: \ dup execute-type drop
    [ dup ] with-datastack ;

M: \ drop execute-type drop
    [ drop ] with-datastack ;

! DEFER: infer-quotation-type ! quotation
M: \ call execute-type drop
    >quotation [ execute-type ] each ;

PREDICATE: empty-quotation < quotation empty? ;
