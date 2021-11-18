USING: accessors arrays combinators continuations effects kernel macros
macros.expander math namespaces quotations sequences tools.continuations
types.algebraic words ;

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

! * Computation-based type transfer description
! The idea is to provide unification infrastructure here for forward/backwards calculations

TUPLE: infer-state undo-quotation typestack rest-quot ;
C: <infer-state> infer-state

: compose-undo ( infer-state undo-quotation -- infer-state )
    [ prepose ] curry change-undo-quotation ;

: prepose-code ( infer-state quot -- infer-state )
    [ prepose ] curry change-rest-quot ;

: next-word ( infer-state -- infer-state word/f )
    dup rest-quot>> [ f f ] [ unclip ] if-empty
    [ [ >>rest-quot ] dip ] [ drop f ] if* ;

: start-infer ( quot -- infer-state )
    [ [ ] { } ] dip <infer-state> ;

PREDICATE: inline-word < word inline? ;

! TODO: cache expansions? based on =, type=?
GENERIC: type-transfer* ( input-typestack word -- quotation undo-quotation )

ERROR: undefined-primitive-type-transfer word ;
: primitive-type-transfer ( typestack word -- quotation undo-quotation )
    { { [ dup \ dup eq? ] [ 2drop [ dup ] [ type-and ] ] }
      { [ dup \ drop eq? ] [ drop { object } ?pop-types nip first 1quotation [ drop ] swap ] }
      { [ dup \ swap eq? ] [ 2drop [ swap ] dup ] }
      [ undefined-primitive-type-transfer ]
    } cond ;

M: \ type-and type-transfer*
    1quotation nip [ dup ] ;


! TODO: emulate =/fail?
! NOTE: We assume a typestack that has types as element types.  The only
! exception here is literal value-level values, which are elevated to literal types
! Also, quotations are not converted here, since they are treated as
! type fragments, i.e. first-class type transfers.
: literal-type-transfer ( typestack thing -- quotation undo-quotation )
    nip
    dup type? [ type-of ] unless 1quotation [ drop ] ;

! ERROR: macro-not-expanded word ;

: element-type-transfer ( typestack word -- quotation undo-quotation )
    { { [ dup primitive? ] [ primitive-type-transfer ] }
      { [ dup word? ] [ type-transfer* ] }
      [ literal-type-transfer ]
    } cond ;

: apply-type-quot ( infer-state quotation -- infer-state )
    '[ _ with-datastack ] change-typestack ;

: pop-macro-literals ( typestack word -- typestack literals )
    macro-effect
    pop-types
    [ value>> ] map ;

: expand-infer-inline ( infer-state typestack word -- infer-state )
    nip def>> prepose-code ;

: expand-infer-macro ( infer-state typestack word -- infer-state )
    [ pop-macro-literals [ >>typestack ] dip ]
    [ macro-quot with-datastack last ] bi
    prepose-code ;

: pad-head-shorter ( seq seq elt -- seq seq )
    [ [ <reversed> ] bi@ ] dip pad-tail-shorter [ <reversed> ] bi@ ;

: pad-typestack ( typestack input-types -- typestack input-types )
    object <atomic> pad-head-shorter ;

! TODO: optimize type-anding only on the common seqence?
: ensure-inputs ( typestack word -- typestack )
    dup word?
    [ stack-effect effect-in-types [ <atomic> ] map
      pad-typestack
      [ type-and ] 2map ] [ drop ] if ;

: infer-step ( infer-state word -- infer-state )
    [ [ ensure-inputs ] curry change-typestack ] keep
    [ dup typestack>> ] dip
    { { [ dup macro? ] [ expand-infer-macro ] }
      { [ dup inline? ] [ expand-infer-inline ] }
      [ element-type-transfer
        [ apply-type-quot ] dip
        compose-undo
      ]
    } cond ;

: run-infer ( infer-step -- infer-step )
    [
        next-word [ infer-step t ]
        [ f ] if*
    ] loop ;

: type-quot-forward ( quot -- infer-state )
    start-infer
    run-infer ;

: reverse-inference ( infer-state -- infer-state )
    \ infer-state unboa spin <infer-state> ;

! Note: only interesting for interface purposes?
: infer-in/out ( quotation -- input-types output-types )
    type-quot-forward
    [ typestack>> ]
    [ reverse-inference run-infer typestack>> ] bi
    swap ;

M: quotation type-of
    infer-in/out <quotation-type> ;

: infer-effect ( quotation -- effect )
    type-of type>class ;
