auto-use
IN: syntax
USE: delegate.private

<< FORGET: POSTPONE: MACRO: >>
<< FORGET: POSTPONE: MACRO:: >>
<< FORGET: POSTPONE: MEMO: >>
<< FORGET: POSTPONE: MEMO:: >>
<< FORGET: POSTPONE: M:: >>
<< FORGET: POSTPONE: IDENTITY-MEMO: >>
<< FORGET: POSTPONE: IDENTITY-MEMO:: >>

<< FORGET: POSTPONE: '[ >>
<< FORGET: POSTPONE: :: >>
<< FORGET: POSTPONE: :> >>
<< FORGET: _ >>
<< FORGET: @ >>
<< FORGET: POSTPONE: [| >>
<< FORGET: POSTPONE: [let >>

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

SYNTAX: [| parse-lambda append! ;

SYNTAX: [let parse-let append! ;

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
 
 "/Users/erg/factor/core/locals" t recursive-directory-files
[ "/Users/erg/factor/core/" ?head drop ] map
[ "." swap subseq? ] reject
[ H{ { CHAR: / CHAR: . } } substitute ] map
[ vocab-exists? ] filter
[ reload ] each 