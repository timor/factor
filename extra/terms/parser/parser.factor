USING: kernel lexer parser words words.symbol vocabs.parser ;

IN: terms.parser

! Allow for parsing unknown term vars inside scope

: define-term-var ( name -- )
    create-word-in [ define-symbol ]
    [ t "term-var" set-word-prop ]
    bi ;

SYNTAX: TERM-VARS: ";" [ define-term-var ] each-token ;


<PRIVATE
SYMBOL: scope-vars

! ! : maybe-parse-term-var ( name -- word/f )
! !     dup first CHAR: ? = not [ drop f ]
! !     ! [ scope-vars get [ <term-var> [ suffix! ] curry define-temp-syntax ] cache ] if ;
! !     [ scope-vars get [ [ create-word ] keep <term-var> [ ] curry ( -- var ) define ] cache ] if ;

<<
! ! Here's how this is supposed to work:
! ! - parser throws no-word-error
! ! - we define the word
! ! - we override the restart handler to create deferred word, which will throw a redefine condition
! ! - we override the redefine condition for the word
! ! - we forget the word at end of scope
! : not-a-hack ( word -- )
!     changed-definitions get sets:delete ;

! : maybe-define-term-var ( name -- ? )
!     dup first CHAR: ? = not [ drop f ]
!     ! [ scope-vars get [ <term-var> [ suffix! ] curry define-temp-syntax ] cache ] if ;
!     ! [ scope-vars get [ [ create-word ] keep <term-var> [ ] curry ( -- var ) define ] cache ] if ;
!     [ [ create-word-in
!         dup scope-vars get push
!       ] keep
!       [ <term-var> [ suffix! ] curry define-syntax ] keepd
!       ! not a hack, nothing to see here:
!       not-a-hack
!       ! <term-var> [ ] curry ( -- term-var ) define-declared
!       t
!     ]
!     if ;

! : no-word-condition? ( error -- ? )
!     { [ condition? ] [ error>> no-word-error? ] } 1&& ;

: maybe-define-term-var ( name -- ? )
    dup first CHAR: ? = not [ drop f ]
    [
        scope-vars get push
    t ] if ;

: override-restart ( condition thing -- * )
    swap continuation>> continue-with ;

GENERIC: override-condition* ( condition error -- * )
M: no-word-error override-condition*
    name>> [ maybe-define-term-var ] keep swap
    [ override-restart ]
    [ drop rethrow ] if ;

! M: redefine-error override-condition*
!     def>> dup scope-vars get member?
!     [ break not-a-hack t override-restart ]
!     [ drop rethrow ] if ;

M: object override-condition* drop rethrow ;

: override-condition ( error/condition -- * )
    dup condition? [ dup error>> override-condition* ]
    [ rethrow ] if ;

! TODO: unintern
: finalize-vars ( vec-of-names -- )
    [
        search
        dup t "term-var" set-word-prop
        dup <wrapper> 1quotation ( -- var ) define-declared
    ] each ;
    ! [ forget ] each ;

>>

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
       recover ] [ scope-vars get finalize-vars ] finally
    ] with-variable ; inline

PRIVATE>

DEFER: TERM> delimiter
SYNTAX: <TERM
    [ [ \ TERM> parse-until ] with-var-defining >quotation ] with-nested-compilation-unit
    ( -- ) call-effect ;
