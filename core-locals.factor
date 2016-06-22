auto-use
IN: syntax
use: delegate.private

COMPILE< forget: postpone\ MACRO: COMPILE>
COMPILE< forget: postpone\ MACRO:: COMPILE>
COMPILE< forget: postpone\ MEMO: COMPILE>
COMPILE< forget: postpone\ MEMO:: COMPILE>
COMPILE< forget: postpone\ M:: COMPILE>
COMPILE< forget: postpone\ IDENTITY-MEMO: COMPILE>
COMPILE< forget: postpone\ IDENTITY-MEMO:: COMPILE>
COMPILE< forget: postpone\ TYPED: COMPILE>
COMPILE< forget: postpone\ TYPED:: COMPILE>

COMPILE< forget: postpone\ '[ COMPILE>
COMPILE< forget: postpone\ :: COMPILE>
COMPILE< forget: postpone\ :> COMPILE>
COMPILE< forget: _ COMPILE>
COMPILE< forget: @ COMPILE>
COMPILE< forget: postpone\ |[ COMPILE>
COMPILE< forget: postpone\ let[ COMPILE>
COMPILE< forget: postpone\ IH{ COMPILE>
COMPILE< forget: postpone\ PROTOCOL: COMPILE>
COMPILE< forget: postpone\ CONSULT: COMPILE>
COMPILE< forget: postpone\ BROADCAST: COMPILE>
COMPILE< forget: postpone\ SLOT-PROTOCOL: COMPILE>
COMPILE< forget: postpone\ HINTS: COMPILE>



SYNTAX: :: (::) define-declared ;
SYNTAX: M:: (M::) define ;
SYNTAX: MEMO: (:) define-memoized ;
SYNTAX: MEMO:: (::) define-memoized ;
SYNTAX: MACRO: (:) define-macro ;
SYNTAX: MACRO:: (::) define-macro ;

SYNTAX: IDENTITY-MEMO: (:) define-identity-memoized ;
SYNTAX: IDENTITY-MEMO:: (::) define-identity-memoized ;

SYNTAX: TYPED: (:) define-typed ;
SYNTAX: TYPED:: (::) define-typed ;

SYNTAX: :>
    in-lambda? get [ :>-outside-lambda-error ] unless
    scan-token parse-def suffix! ;

SYNTAX: |[ parse-lambda append! ;

SYNTAX: let[ parse-let append! ;

SYNTAX: MEMO[ parse-quotation dup infer memoize-quot suffix! ;

SYNTAX: '[ parse-quotation fry append! ;
: _ ( -- * ) "Only valid inside a fry" throw ;
: @ ( -- * ) "Only valid inside a fry" throw ;
PREDICATE: fry-specifier < word { _ @ } member-eq? ;

SYNTAX: IH{ \ } [ >identity-hashtable ] parse-literal ;


SYNTAX: PROTOCOL:
    scan-new-word parse-definition define-protocol ;
    
SYNTAX: CONSULT:
    scan-word scan-word parse-definition <consultation>
    [ save-location ] [ define-consult ] bi ;

SYNTAX: BROADCAST:
    scan-word scan-word parse-definition <broadcast>
    [ save-location ] [ define-consult ] bi ;


SYNTAX: SLOT-PROTOCOL:
    scan-new-word ";"
    [ [ reader-word ] [ writer-word ] bi 2array ]
    map-tokens concat define-protocol ;
    
    
SYNTAX: HINTS:
    scan-object dup wrapper? [ wrapped>> ] when
    [ changed-definition ]
    [ subwords [ changed-definition ] each ]
    [ parse-definition { } like set-specializer ] tri ;
    
    


 H{ } clone root-cache set-global
 
 use: io.directories.search
 "/Users/erg/factor/core/locals" t recursive-directory-files
[ "/Users/erg/factor/core/" ?head drop ] map
[ "." swap subseq? ] reject
[ H{ { char: / char: . } } substitute ] map
[ vocab-exists? ] filter
[ reload ] each


 use: io.directories.search
 use: ui.tools.listener
 "/Users/erg/factor/core/stack-checker" t recursive-directory-files
[ "/Users/erg/factor/core/" ?head drop ] map
[ "." swap subseq? ] reject
[ H{ { char: / char: . } } substitute ] map
[ vocab-exists? ] filter
[ reload ] each



"fry" reload
"bootstrap.image" reload


! load somewhere!
{
    { [ os windows? ] [ "alien.libraries.windows" ] }
    { [ os unix? ] [ "alien.libraries.unix" ] }
} cond require


! bug in locals with current approach...
"compiler.cfg.parallel-copy" reload


MD5 (boot.unix-x86.64.image) = 9fa82ffeeb8eebf763327205a78c4597



 "/Users/erg/factor/core/" t recursive-directory-files
[ "/Users/erg/factor/core/" ?head drop ] map
[ "." swap subseq? ] reject
[ H{ { char: / char: . } } substitute ] map
[ vocab-exists? ] filter



string-lines
[ " " split1 nip ] map
[ "resource:core/" ?head drop ] map
[ H{ { char: / char: . } } substitute ] map
[ "." split but-last but-last  "." join ] map

2dup diff


    "compiler"
    "command-line.debugger"
    "command-line.startup"
    "delegate.protocols"
    "locals.definitions"
    "memoize.syntax"
    "typed.debugger"
    "typed.namespaces"
    "hashtables.identity.mirrors"
    "vocabs.loader.test.a"
    "vocabs.loader.test.b"
    "vocabs.loader.test.c"
    "vocabs.loader.test.d"
    "vocabs.loader.test.e"
    "vocabs.loader.test.f"
    "vocabs.loader.test.g"
    "vocabs.loader.test.h"
    "vocabs.loader.test.i"
    "vocabs.loader.test.j"
    "vocabs.loader.test.k"
    "vocabs.loader.test.l"
    "vocabs.loader.test.m"
    "vocabs.loader.test.n"
    "vocabs.loader.test.o"
    "vocabs.loader.test.p"
    

disable-optimizer
enable-optimizer
    
IN: scratchpad 1 1 - restarts [ nth f ] change-global  "peg.ebnf" reload continue-restart
