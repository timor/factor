USING: accessors continuations generic kernel namespaces sequences sets
tools.continuations words ;

IN: prefix-syntax


TUPLE: let-expr name expression ;
C: <let> let-expr

! Non-Inlining
! Non-modifying
! Does not walk into quotations on its own
: walk-words ( quotation quot: ( rest word -- rest ) -- )
    over empty? [ 2drop ]
    [ [ unclip ] dip [ call( ..a rest word -- ..b rest ) ] keep walk-words
    ] if ;

SYMBOL: inline-mode
SINGLETON: inline-base
HOOK: inline-word? inline-mode ( word -- ? )
HOOK: inline-def inline-mode ( word -- def )
M: f inline-word? inline? ;
M: f inline-def def>> ;
M: inline-base inline-word?
    { [ generic? not ] [ quotation? not ] } 1&& ;
GENERIC: recursive-def>> ( object -- definition )
M: word recursive-def>> def>> ;
M: object recursive-def>> 1quotation ;
M: inline-base inline-def
    recursive-def>> ;

ERROR: recursive-inline-walk trace word ;
SYMBOL: history

: note-recursive ( word -- )
    history [ swap suffix ] change ;
    ! [ history [ over suffix ] change ] prepose ;

: when-recursive ( quot rec-quot -- quot )
    swap '[ dup history get in? [ history get swap @ ] _ if ] ;

: err-recursive ( quot -- quot )
    [ history get swap recursive-inline-walk ] when-recursive ;

! This version works with internal error handling
: walk-words-inline ( quotation quot: ( rest word -- rest ) -- )
    dup '[ dup inline-word? [ [ [ note-recursive ] [ def>> ] bi _ walk-words-inline ] with-scope ] err-recursive _ if ] walk-words ;

: same-recursive-inline-walk? ( error -- ? )
    dup recursive-inline-walk?
    [ word>> history get last = ]
    [ drop f ] if ;

! This version is intended to backtrack to the recursive word in question
:: walk-words-inline-rec ( words quot: ( rest word -- rest ) rec-quot: ( rest word -- rest ) -- )
    words [ dup inline-word? [
                [ [ [ note-recursive ] [ inline-def ] bi quot rec-quot walk-words-inline-rec ]
                  [ dup same-recursive-inline-walk? [ drop ] rec-quot compose [ rethrow ] if ] recover ] with-scope
            ] err-recursive
            quot if ] walk-words ;

