USING: accessors assocs combinators compiler.units continuations kernel lexer
namespaces parser quotations sequences vocabs vocabs.parser words words.symbol ;

IN: terms.parser

! Allow for parsing unknown term vars inside scope

: define-term-var ( name -- )
    create-word-in [ define-symbol ]
    [ t "term-var" set-word-prop ]
    bi ;

SYNTAX: TERM-VARS: ";" [ define-term-var ] each-token ;


<PRIVATE
SYMBOL: scope-vars

! Here's how this is supposed to work:
! - parser throws no-word-error
! - we override the restart handler to create deferred word
! - at end of scope, define the words, unintern them

: maybe-define-term-var ( name -- ? )
    dup first CHAR: ? = not [ drop f ]
    [ scope-vars get push t ] if ;

: override-restart ( condition thing -- * )
    swap continuation>> continue-with ;

GENERIC: override-condition* ( condition error -- * )
M: no-word-error override-condition*
    name>> [ maybe-define-term-var ] keep swap
    [ override-restart ]
    [ drop rethrow ] if ;

M: object override-condition* drop rethrow ;

: override-condition ( error/condition -- * )
    dup condition? [ dup error>> override-condition* ]
    [ rethrow ] if ;

: unintern ( word -- )
    dup vocabulary>> [ [ name>> ] dip vocab-words-assoc delete-at ] keepd
    f >>vocabulary drop ;

: finalize-vars ( vec-of-names -- )
    [ search 
      [ t "term-var" set-word-prop ]
      [ dup <wrapper> 1quotation ( -- var ) define-declared ]
      [ unintern ] tri
    ] each ;

: with-var-defining ( quot -- )
    V{ } clone scope-vars rot
    '[ [ _
       [ override-condition ]
       recover ] [ scope-vars get finalize-vars ] finally
    ] with-variable ; inline

PRIVATE>

DEFER: TERM> delimiter
SYNTAX: <TERM
    [ [ \ TERM> parse-until ] with-var-defining >quotation ] with-nested-compilation-unit
    ( -- ) call-effect ;
