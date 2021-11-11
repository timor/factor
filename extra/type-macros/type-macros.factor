USING: accessors classes combinators continuations effects kernel
macros.expander quotations sequences variants words ;

IN: type-macros

! * Type-level macros

! ** Representation
VARIANT: datatype
    literal: { { class maybe{ class } } value }
    class-type: { { class maybe{ class } } }
    ;

! ** Transfer computation

! We assume a model of "code" filtering for (pre-)compilation:
! While iterating over the source quotation, ~type-transfer~ with effect
! ~( typestack word -- typestack )~ calculates the new state of the type stack.
! After that, ~code-transfer~ with effect
! ~( quotation-accum typestack word -- quotation-accum )~ is used to append the
! correct code to the current output quotation.  For constants, this is simply
! appending the literal value (which will push itself once called).  The same is
! true for regular words.  Inline words will append their body to the quotations.
! All of the above do not need to make use of the type stack for quotation
! building.

! The typestack is needed as non-trivial input to ~code-transfer~ for
! 1. Expanding Macros - There we need the literal arguments from the type stack to
!    feed to the expander, which is applied to the current quotation in
!    ~code-transfer~.  Note that there is technically no need to use the type stack for this
!    case, as the literal elements will be present as tail of the quotations.  But
!    since we track literal values on the type stack, we take them from there.
! 2. Expanding Type Macros - We dispatch on the top contents of the type stack,
!    so the expansion function is chosen generically.

!    TODO: there are a couple of approaches this could be formalized/defined:
!    1. Regular generic dispatch - In most cases, we really would liked to have
!       multi dispatch, so this will transfer the same problems we have when
!       expressing generic data-level dispatch without multiple dispatch
!       capabilities to the macro expansion domain.
!    2. Multiple generic dispatch - Would have to be simulated, as there is
!       currently no built-in functionality.  Care must be taken to have
!       sequential or parallel precedence rules regarding dispatch tuple subtyping
!    3. Pattern Matching - Requires structural representations of objects on the
!       type stack, i.e. some form of structural typing.  Also, this would
!       probably mean defining the dispatch decision for a single word inside a
!       single statement, as only that way it is guaranteed that the conditions
!       are tried in a unique order, to be specified by the programmer.
! 3. Inlining regular Generic dispatch - Inlining generic dispatch when it is
!    known that only a subset (ideally one) of the methods are applicable.
!    I.e. compile-time dispatch has the same semantics as a type macro, albeit
!    without the capability to actually manipulate the resulting quotation.

! A kind of call which is called on type stacks, not data stacks
! TODO: have to handle recursives correctly here?
GENERIC: type-transfer ( input-type-stack word -- output-type-stack )
GENERIC: generate-code ( quotation-accum input-type-stack word -- new-code recursive? )

! : compute-type-transfer ( configuration code -- configuration )
!     [ type-transfer ] each ;
! : compute-code-transfer ( quotation configuration code -- quotation )
!     [ generate-code ] each ;

! : type-config ( quotation -- configuration )
!     { } swap compute-type-transfer ;

! TODO insert checks here for existing effects?
: assume-input-configuration ( typestack configuration -- typestack )
    2dup longer? [ length head-slice* ]
    [ 2drop { } ] if ;
: normal-word-transfer-type ( typestack word -- typestack )
    stack-effect
    [ effect-in-types assume-input-configuration ]
    [ effect-out-types append ] bi ;

PREDICATE: shuffle-word < word "shuffle" word-prop ;

! NOTE If we want to allow compilation mode switching, this would be made a hook
! generic to change what is the current macro base!
: base-combinator? ( word -- ? )
    { call ? curry compose boa
    } member-eq? ;

GENERIC: base-type-transfer ( typestack )

M: word type-transfer
    {
        { [ shuffle-word? ] [ "shuffle" word-prop shuffle ] }
      { [ dup base-combinator? ] [ base-type-transfer ] }
      [ normal-word-transfer-type ]
    } cond ;

M: object type-transfer
    [ class-of ] keep <literal> suffix ;

M: object generate-code
    2nip 1quotation f ;

PREDICATE: type-macro < word "type-expander" word-prop ;

GENERIC: generate-macro-code ( quotation typestack word -- quotation )

! Macros and compile-transform defined
ERROR: non-literal-macro-arguments configuration n ;
: pop-literals ( configuration n -- inputs )
    tail-slice* dup [ literal? ] all?
    [ [ value>> ] map ]
    [ non-literal-macro-arguments ] if ;

: pop-inputs ( quotation configuration quot -- quotation configuration inputs )
    dupd macro-effect pop-literals ;

! Regular Macros
M: word generate-macro-code
    dup macro-quot
    [ [ pop-inputs cut-slice ] dip with-datastack ]
    [ drop ] if* ;

! Type Macros
M: type-macro generate-macro-code


! Note: we allow recursive macros here!
M: word generate-code
    { { [ dup type-macro? ] [ generate-macro-code t ] }
      { [ dup macro-quot ] [ generate-macro-code t ] }
      [ call-next-method ]
    } cond ;


! 1. Compute the new typestack
! 2. Return piece of code

! code transfer returns a flag indicating whether to simply append the code or
! expand recursively.

DEFER: expand-code
: expand-step ( current-quotation typestack word -- current-quotation typestack )
    [ type-transfer ] keep
    [ generate-code ] keepd swap
    ;

: expand-code ( current quotation typestack quotation -- current-quotation typestack )
    [ expand-step ] each ;

: expand ( code -- current-quotation typestack )
    [ { } { } ] dip expand-code ;
