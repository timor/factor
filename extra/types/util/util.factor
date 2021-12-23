USING: accessors assocs colors.constants combinators.short-circuit io io.styles
kernel math math.parser namespaces prettyprint.backend prettyprint.custom
prettyprint.sections quotations sequences sequences.private strings unicode
words ;

IN: types.util

TUPLE: mapped
    { seq sequence read-only }
    { at-quot maybe{ callable } read-only } ;

C: <mapped> mapped

INSTANCE: mapped immutable-sequence
M: mapped length seq>> length ;
M: mapped nth-unsafe
    [ seq>> nth-unsafe ]
    [ at-quot>> call( elt -- elt ) ] bi ;

! Like 2map, but will return prefix of longer sequence prepended
! 2map ( ... seq1 seq2 quot: ( ... elt1 elt2 -- ... newelt ) -- ... newseq )

: 2map-suffix ( ... seq1 seq2 quot: ( ... elt1 elt2 -- ... newelt ) -- ... newseq )
    [
        2dup longer? [ swap ] when
        2dup [ length ] bi@ swap -
        cut-slice swap
    ] dip swap
    [ 2map ] dip prepend ; inline

: each-with-rest ( ... seq quot: ( ... rest elt -- ... ) -- ... )
    [ [ length ] keep ] dip
    '[
        _ [ swap tail-slice ] [ nth ] 2bi @
    ] each-integer ; inline

: ?shorter ( seq1 <seq2 -- n/f )
    2dup shorter?
    [ [ length ] bi@ swap - ]
    [ 2drop f ] if ;

: ?missing ( seq n -- seq n/f )
    dupd [ length ] dip - dup 0 < [ neg ] [ drop f ] if ;

! ! Used for macros?
! : fold-call ( ..a quot: ( ..a -- ..b quot: ( ..b -- ..c ) ) -- ..b quot: ( ..b -- ..c ) )
!     call ; inline foldable


: at? ( key assoc -- value/key key/f )
    [ ?at ] keepd and ;

: cut-when* ( ... seq quot: ( ... elt -- ... ? ) -- ... before after )
    [ [ <reversed> ] dip find drop ] keepd swap
    [ cut* ] [ f over like ] if* ; inline

! * Unique var names
! For the thousandths time...
MIXIN: id-name
: name-ize ( str -- str )
    dup [ digit? ] all? [ "_" append ] when ; inline
: string>id-name ( str -- name-part id-part/f )
    name-ize [ digit? not ] cut-when* [ f ] when-empty ; foldable
! PREDICATE: varname-string < string string>id-name  ;
INSTANCE: string id-name
GENERIC: name-part ( id-name -- str )
GENERIC: id-part ( id-name -- id/f )
GENERIC#: <id-name> 1 ( id-name id -- id-name )
M: string name-part string>id-name drop ; inline
M: string id-part string>id-name nip ; inline
M: string <id-name> [ name-part ] dip number>string append ;

SYMBOL: var-names

: reset-var-names ( -- )
    var-names H{ } clone set ;

: with-var-names ( quot -- )
    [ H{ } clone var-names ] dip
    with-variable ; inline

: get-name-suffix ( key -- name )
    dup name-part var-names get at <id-name> ;

: uvar ( key -- name )
    [ name-part var-names get inc-at ]
    [ get-name-suffix ] bi ;

: uvar-shuffle ( in out -- in out )
    [ [ uvar ] map ] dip
    [ get-name-suffix ] map ;

! ! * Prettyprinting compact stuff
TUPLE: separator-block < flow separator ;
: <separated-block> ( separator -- obj )
    dup length separator-block
    new-section V{ } clone >>sections
    swap >>separator ;

: <separated ( separator -- )
    <separated-block> (<block) ;

M: separator-block advance
    dup {
        [ start>> pprinter get last-newline>> = not ]
        [ short-section? ]
    } 1&& swap separator>> '[ H{ { foreground COLOR: solarized-base0 } } [ _ write ] with-style ] when ;

: <nosep ( -- )
    "" <separated ;

: delim-text ( start? obj -- )
    [ dup word? [ pprint-word drop ] [ text [ start-group ] [ end-group ] if ] if ] [ drop ] if* ;

: pprint-compact ( object separator -- )
    '[
        <nosep
        ! <flow
        dup pprint-delims [
            <nosep
            dup pprint-narrow? <inset
            <nosep t swap delim-text block>
            <nosep
            >pprint-sequence

            do-length-limit
            [ [ _ <separated pprint* block> ] each ] dip
            [ number>string "~" " more~" surround text ] when*

            block>
            block>
            block>
        ] dip <nosep f swap delim-text block>
        end-group
        block>
        ! block>
    ] check-recursion ;
