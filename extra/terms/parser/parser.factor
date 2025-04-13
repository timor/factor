USING: accessors assocs combinators combinators.short-circuit compiler.units
continuations definitions kernel namespaces parser quotations sequences sets
terms tools.continuations vocabs.parser words ;

IN: terms.parser

! Allow for parsing unknown term vars inside scope

<PRIVATE
SYMBOL: scope-vars

! : maybe-parse-term-var ( name -- word/f )
!     dup first CHAR: ? = not [ drop f ]
!     ! [ scope-vars get [ <term-var> [ suffix! ] curry define-temp-syntax ] cache ] if ;
!     [ scope-vars get [ [ create-word ] keep <term-var> [ ] curry ( -- var ) define ] cache ] if ;

<<
! Here's how this is supposed to work:
! - parser throws no-word-error
! - we define the word
! - we override the restart handler to create deferred word, which will throw a redefine condition
! - we override the redefine condition for the word
! - we forget the word at end of scope
: not-a-hack ( word -- )
    changed-definitions get sets:delete ;

: maybe-define-term-var ( name -- ? )
    dup first CHAR: ? = not [ drop f ]
    ! [ scope-vars get [ <term-var> [ suffix! ] curry define-temp-syntax ] cache ] if ;
    ! [ scope-vars get [ [ create-word ] keep <term-var> [ ] curry ( -- var ) define ] cache ] if ;
    [ [ create-word-in
        dup scope-vars get push
      ] keep
      [ <term-var> [ suffix! ] curry define-syntax ] keepd
      ! not a hack, nothing to see here:
      not-a-hack
      ! <term-var> [ ] curry ( -- term-var ) define-declared
      t
    ]
    if ;

: no-word-condition? ( error -- ? )
    { [ condition? ] [ error>> no-word-error? ] } 1&& ;

: override-restart ( condition thing -- * )
    swap continuation>> continue-with ;

GENERIC: override-condition* ( condition error -- * )
M: no-word-error override-condition*
    name>> [ maybe-define-term-var ] keep swap
    [ override-restart ]
    [ drop rethrow ] if ;

M: redefine-error override-condition*
    def>> dup scope-vars get member?
    [ break not-a-hack t override-restart ]
    [ drop rethrow ] if ;

M: object override-condition* drop rethrow ;

: override-condition ( error/condition -- * )
    dup condition? [ dup error>> override-condition* ]
    [ rethrow ] if ;

: forget-vars ( vars -- )
    [ forget ] each ;

>>

! TODO: finally forget
: with-var-defining ( quot -- )
    ! H{ } clone scope-vars rot
    V{ } clone scope-vars rot
    '[ [ _
       ! [ dup no-word-condition? [ break dup [ error>> name>> maybe-parse-term-var ] [ rethrow ] if ] [ rethrow ] if ]
       ! [| con | con no-word-condition?
       !  [
       !      con error>> name>> maybe-parse-term-var :> w
       !      w con override-restart
       !  ]
       !  [ con rethrow ] if ]
       [ override-condition ]
       recover ] [ scope-vars get forget-vars ] finally
    ] with-variable ; inline

PRIVATE>

DEFER: TERM> delimiter
SYNTAX: <TERM 
    [ [ \ TERM> parse-until ] with-var-defining >quotation ] with-nested-compilation-unit
    ( -- ) call-effect ;
