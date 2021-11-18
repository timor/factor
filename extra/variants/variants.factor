! Copyright (C) 2009 Joe Groff.
! See http://factorcode.org/license.txt for BSD license.
USING: accessors arrays classes classes.mixin classes.parser classes.singleton
classes.tuple classes.tuple.parser combinators inverse kernel lexer make parser
quotations sequences slots splitting words ;
IN: variants

PREDICATE: variant-class < mixin-class "variant?" word-prop ;

M: variant-class initial-value*
    class-members [ f f ] [
        first dup word? [ t ] [ initial-value* ] if
    ] if-empty ;

: define-tuple-class-and-boa-word ( class superclass slots -- )
    pick [ define-tuple-class ] dip
    dup name>> "<" ">" surround create-word-in swap define-boa-word ;

: define-variant-member ( member -- class )
    dup array? [ first3 pick [ define-tuple-class-and-boa-word ] dip ] [ dup define-singleton-class ] if ;

: define-variant-class ( class -- )
    [ define-mixin-class ] [ t "variant?" set-word-prop ] bi ;

: define-variant-class-member ( class member -- )
    define-variant-member swap add-mixin-instance ;

: define-variant-class-members ( class members -- )
    [ dup define-variant-class ] dip
    [ define-variant-class-member ] with each ;

: parse-variant-tuple-member ( name -- member )
    create-class-in tuple
    "{" expect
    [ "}" parse-tuple-slots-delim ] { } make
    3array ;

: parse-variant-member ( name -- member )
    ":" ?tail [ parse-variant-tuple-member ] [ create-class-in ] if ;

: parse-variant-members ( -- members )
    [ scan-token dup ";" = not ]
    [ parse-variant-member ] produce nip ;

SYNTAX: VARIANT:
    scan-new-class
    parse-variant-members
    define-variant-class-members ;

SYNTAX: VARIANT-MEMBER:
    scan-word
    scan-token parse-variant-member
    define-variant-class-member ";" expect ;

MACRO: unboa ( class -- quot )
    <wrapper> \ boa [ ] 2sequence [undo] ;

GENERIC#: (match-branch) 1 ( class quot -- class quot' )

M: singleton-class (match-branch)
    \ drop prefix ;
M: object (match-branch)
    over \ unboa [ ] 2sequence prepend ;

: ?class ( object -- class )
    dup word? [ class-of ] unless ;

: match-expansion ( spec -- quot )
    [ dup callable? [ first2 (match-branch) 2array ] unless ] map
    [ \ dup \ ?class ] dip \ case [ ] 4sequence ;

GENERIC: cond-match-prefix ( class -- quot )
M: singleton-class cond-match-prefix
    drop [ drop ] ;
M: object cond-match-prefix
    \ unboa [ ] 2sequence ;

: cond-match-branch ( class quot -- cond-quot then-quot )
    [ dup cond-match-prefix ] dip compose
    [ \ dup swap \ instance? [ ] 3sequence ] dip ;

: cond-match-expansion ( branches -- quot )
    [ dup callable? [ first2 cond-match-branch 2array ] unless ] map
    [ cond ] curry ;

MACRO: match ( branches -- quot )
    cond-match-expansion ;
