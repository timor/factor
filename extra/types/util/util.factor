USING: accessors arrays assocs classes classes.algebra classes.algebra.private
classes.mixin classes.singleton classes.union colors.constants combinators
combinators.short-circuit combinators.smart generalizations graphs
graphs.private io io.styles kernel lists lists.private make math math.parser
mirrors namespaces prettyprint.backend prettyprint.custom prettyprint.sections
quotations sequences sequences.extras sequences.private sets threads typed words
;

IN: types.util

FROM: syntax => _ ;

TUPLE: mapped
    { seq sequence read-only }
    { at-quot maybe{ callable } read-only } ;

C: <mapped> mapped

INSTANCE: mapped immutable-sequence
M: mapped length seq>> length ; inline
M: mapped nth-unsafe
    [ seq>> nth-unsafe ]
    [ at-quot>> call( elt -- elt ) ] bi ; inline

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

! * Working with typed lists
PREDICATE: lmatch-pair < pair first2 [ classoid? ] [ callable? ] bi* and ;
PREDICATE: lmatch-specs < sequence unclip-last { [ drop [ lmatch-pair? ] all? ]
                                                 [ nip union{ callable lmatch-pair } instance? ] } 2&& ;
GENERIC: lmatch-branch-cond ( branch-spec -- quot )
M: callable lmatch-branch-cond drop [ t ] ;
M: lmatch-pair lmatch-branch-cond first '[ dup _ instance? ] ;
GENERIC: lmatch-branch-body ( branch-spec -- quot )
M: callable lmatch-branch-body ;
M: lmatch-pair lmatch-branch-body second ;
TYPED: lmatch-branches ( branches: lmatch-specs -- branches )
    [ [ lmatch-branch-cond ] [ lmatch-branch-body ] bi 2array ] map ;

TYPED: wrap-nil-lmatch ( nil-case: callable branches -- quot )
    '[
        dup +nil+?
        [ drop @ ]
        [ unswons _
          cond ] if
    ] ;
    ! swap [ drop ] prepose [ dup +nil+? ] swap 2array prefix ;

MACRO: lmatch ( nil-case branches -- quot )
    lmatch-branches wrap-nil-lmatch ;
    ! prepend-nil-case '[
    !     _ cond
    ! ] ;

: dipd ( ..a x y quot: ( ..a y -- ..b ) -- ..b x )
    rot [ call ] dip ; inline

! Typed conses
GENERIC: swons* ( cdr car class -- cons )
M: \ cons-state swons* drop swons ;
: cons* ( car cdr class -- cons )
    [ swap ] dip swons* ; inline

: lreverse-as ( list cons-class -- new-list )
    nil swap '[ _ swons* ] foldl ;

: lmap-as ( ... list quot: ( ... elt -- ... newelt ) cons-class -- ... result )
    [ [ nil ] dip ] dip [ '[ swapd dip _ cons* ] curry foldl ] keep lreverse-as ; inline

MACRO: lmatch-map-as ( branches cons-class -- quot )
    [ lmatch-branches ] dip
    '[ [ _ cond ] _ lmap-as ] ;

! MACRO: lmatch-filter ( cases -- quot )
!     dup [ first2 '[ _ dipd cons ] 2array ] map
!     '[ [ +nil+ ]
!        _ lmatch
!     ] ;

: list-class ( list -- class )
    dup { [ nil? ] [ list? not ] } 1|| [ drop cons-state ]
    [ class-of ] if ;


! Improper lists
: list* ( list cdr -- list* )
    2dup [ list-class ] bi@ class-and
    '[ _ swons* ] foldr ;

: leach* ( ... list* quot: ( ... elt -- ... ) -- ... )
    over atom? [ 2drop ] [ (leach) leach* ] if ; inline recursive

: llength* ( list* -- n )
    0 [ drop 1 + ] swapd leach* ;
    ! 0 [ drop 1 + ] swapd over atom? [ 2drop ] [ (leach) leach ] if ;

: list>array* ( list* -- array )
    [ [ , ] leach* ] {  } make ;

:: lany?* ( l* quot: ( elt -- ? ) -- ? )
    l* dup atom? [ drop f ]
    [ unswons quot call( elt -- ? ) [ nip ] [ quot lany?* ] if* ] if ;

: lastcdr ( list -- x )
    dup atom? [ cdr lastcdr ] unless ; inline recursive

: list*>array ( list* -- array )
    [ list>array* ] [ lastcdr ] bi suffix ;

! Check for compatible list prefix, return longer one if match
: list~ ( list1 list2 -- list/f )
    { [ t [ = and ] 2lreduce ] [ [ [ llength ] bi@ > ] most ] } 2&& ;

! ! Same, but return shorter one
! : list~< ( list1 list2 -- list/f )
!     { [ t [ = and ] 2lreduce ] [ [ [ llength ] bi@ < ] most ] } 2&& ;


! * Cache with hit indicator

:: ?cache ( ... key assoc quot: ( ... key -- ... value ) -- ... value hit? )
    key assoc at* :> ( val hit? )
    hit? [ val t ]
    [ key quot call( ... key -- ... value ) [ key assoc set-at ] keep f ] if ; inline

! * Preventing loop freezes
: co-loop ( ... pred: ( ... -- ... ? ) -- ... )
    [ yield ] compose loop ; inline

! * (Re-)Construction
: 2assoc-all? ( a1 a2 quot: ( v1 v2 -- ? ) -- ? )
    2over [ assoc-size ] same? not [ 3drop f ]
    [| a1 a2 quot |
     a1 [| k1 v1 | k1 a2 at v1 quot call( x x -- ? ) ] assoc-all?
    ] if ;

: slots-equiv? ( obj obj quot: ( slot slot -- ?  ) -- ? )
    [ [ <mirror> ] bi@ ] dip 2assoc-all? ;

: tuple-slots-eq? ( obj obj -- ? )
    { [ [ class-of ] same? ] [ [ eq? ] slots-equiv? ] } 2&& ;

:: neq? ( n -- quot )
    [ [ eq? ] 2 n mnapply ] [ and ] reduce-outputs ; inline

:: ?rebuild ( ..a orig decons: ( ..a orig -- ..b ) quot: ( ..b -- ..c ) recons: ( ..c -- ..d obj ) -- ..d obj )
    decons outputs :> n
    orig decons call
    quot [ ] n nbi
    ! quot n nkeep
    [ n neq? ] n ncurry preserving
    [ n ndrop orig ]
    recons if ; inline

:: with-bi@ ( param x y quot --  )
    param x quot with call
    param y quot with call ; inline

: remove-nths ( indices seq -- seq )
   [ swap in? not nip ] with filter-index ; inline

! * Finding subterms
! Things can either returns childs or be an atom
! If returning empty sequence, don't keep tracking
! If returning f, treat as atom
! Test is only called on atoms

:: (deep-find-all) ( obj destructure: ( obj -- elts ) test: ( obj -- ? ) -- )
    ! obj test call( obj -- ? ) [ , ] [ drop ] when
    obj [| o | o destructure call( obj -- elts ) :> elts
         elts [ o test call( obj -- ? ) [ o , ] when f ] unless*
    ] closure drop ;

: deep-find-all ( obj destructure: ( obj -- elts ) test: ( obj -- ? ) -- elts )
    [ (deep-find-all) ] { } make ;

! Returns the object for which the test returns true
! objects themselves are not tested
:: deep-find-elt ( obj destructure: ( obj -- elts ) test: ( elt -- ? ) -- obj )
    obj destructure call( obj -- elts ) :> elts
    elts [ f ] [ [ test call( obj -- ? ) ] any? [ obj ] [ elts [ destructure test deep-find-elt ] find nip ] if ] if-empty ;

! * Forest Closure

:: forest-as ( vertices quot: ( vertex -- edges ) exemplar -- set )
    exemplar new-empty-set-like :> s
    vertices [ dup s in? [ drop ] [ s quot (closure) ] if ] each
    s ; inline

! * Class simplification
:: simplify-neg-intersection ( neg -- classes removed? )
    neg
    [| ca |
         neg [| cb | ca cb class< ] find nip
    ] find :> ( i found? )
    found? [ i neg remove-nth ] [ neg ] if
    found? ;

: simplify-intersection ( classes -- classes )
    [ anonymous-complement? not ] partition
    [ class>> ] map [ simplify-neg-intersection ] loop
    [ class-not ] map
    append [ ] [ class-and ] map-reduce ;

! TODO maybe cache

GENERIC: simplify-class ( class -- class )

! Hack? I don't see any hack here... *whistle*
M: W{ union{ fixnum bignum } } simplify-class
    drop integer ;

! NOTE: this could be important for handling nominative unions/intersections
! Non-normalizing behavior does not convert defined
! union/intersection classes to anonymous intersections

M: classoid simplify-class ;
! NOTE: the normal form here is the non-wrapped version!
! FIXME: This is wrong!
! M: wrapper simplify-class
!     dup wrapped>>
!     {
!         { [ dup singleton-class? ] [ nip ] }
!         { [ dup not ] [ 2drop \ f ] }
!         [ drop ]
!     } cond ;
M: wrapper simplify-class ;

M: anonymous-intersection simplify-class
    participants>> [ simplify-class ] map
    simplify-intersection ;

! not{ union{  } } constructs are converted to intersection{ not{  } }
! constructs.  But not the other way round, since we would run into endless loops?
M: anonymous-complement simplify-class
    class>> simplify-class
    dup anonymous-union?
    [ members>> [ class-not ] map simplify-intersection ]
    [ class-not ] if ;

: simplify-member-classes ( x -- x )
    class-members
    [ null ]
    [ [ simplify-class ] [ class-or ] map-reduce ] if-empty ;

! NOTE: not expanding simple named unions, since this doesn't give any benefits right now
! M: union-class simplify-class
!     simplify-member-classes ;
M: union-class simplify-class ;

! NOTE: this is different from factor's behavior, which does not expand mixins
M: mixin-class simplify-class
    simplify-member-classes ;

: expand-intersection ( union-class intersections -- class intersections ? )
    dup empty? [ f ]
    [ unclip [ participants>>
          [ class-or ] with [ class-and ] map-reduce
       ] dipd t ] if ;

M: anonymous-union simplify-class
    members>> [ simplify-class ] map
    [ anonymous-intersection? ] partition
    null [ class-or ] reduce swap
    [ expand-intersection ] loop drop ;

: simplifying-class-and ( class1 class2 -- class )
    class-and simplify-class ;

: simplifying-class-or ( class1 class2 -- class )
    class-or simplify-class ;
