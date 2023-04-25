USING: accessors arrays assocs assocs.extras chr chr.programs classes
classes.algebra classes.tuple classes.tuple.private combinators.short-circuit
kernel linked-assocs math quotations sequences sets stack-checker terms vectors
;

IN: chr.programs.incremental

: insert-existential-generators ( rule -- rule )
    clone
    dup rule-existentials insert-generators! ;

: annotate-heads ( rule -- seq )
    [ nkept>> ] [ heads>> ] bi
    [ > swap 2array ] with map-index ;

: distribute-heads ( seq -- seq )
    dup [
         remove-nth
         2array
    ] curry map-index ;

: matchable-head? ( sub-pred type -- ? )
    swap
    { [ drop classoid? ] [ class>> classes-intersect? ] } 2&& ;

GENERIC#: push-at-constraint-type 1 ( elt type index -- )

! When indexing a sub-pred head, add to existing known matching classes
: push-at-applicable ( elt type index -- )
    3dup push-at
    [ ! | itype elt type seq |
        [ rot matchable-head? ] dip swap
        [ push ] [ 2drop ] if
    ] 2with assoc-each ;

! When indexing a classoid type head, initialize with all matching chr-sub-defs if necessary
: maybe-match-sub-preds ( class index -- )
    2dup key? [ 2drop ] [
        [
            [ drop { [ drop chr-sub-pred? ] [ swap class>> classes-intersect? ] } 2&& ] with assoc-filter values concat
            >vector
        ] 2keep set-at
    ] if ;

PREDICATE: tuple-chr-sub-pred < chr-sub-pred class>> tuple-class? ;
M: chr-sub-pred push-at-constraint-type push-at-applicable ;
M: tuple-chr-sub-pred push-at-constraint-type
    3dup push-at
    [ class>> subclasses ] dip [ push-at-constraint-type ] curry with each ;
M: object push-at-constraint-type push-at ;
M: classoid push-at-constraint-type
    2dup maybe-match-sub-preds
    push-at ;


TUPLE: reflexive-parms { parms read-only } ;
: match-spec-args ( head -- spec )
    [ constraint-args ] keep
    reflexive? [ reflexive-parms boa ] when ;

GENERIC: match-class ( head -- class )
M: chr-pred match-class class-of ;
M: as-pred match-class pred>> match-class ;
M: chr-sub-pred match-class class>> ;
M: pred-array match-class first ;
M: fiat-pred-array match-class first ;

: match-head-class-arities ( partner-entries -- assoc )
    [ second match-class ] collect-by [ length ] map-values ;

:: add-heads ( program rule rule-ind entries -- program )
    entries <enumerated> >alist <reversed>
    [| hi ent |
     rule-ind hi 2array :> occ
     ent first2 :> ( aent partners )
     aent first2 :> ( hkept h )
     h constraint-type :> type
     occ type program occur-index>> push-at-constraint-type
     occ hkept h match-spec-args partners rule match-vars>>
     partners match-head-class-arities
     <constraint-schedule>
     type program schedule>> push-at-constraint-type
    ] assoc-each
    program
    ;

:: add-to-index ( program rule -- program )
    program rule
    program rules>> length
    rule annotate-heads distribute-heads
    add-heads ;

: add-vars ( program rule -- program )
    term-vars [ union ] curry change-local-vars ;

: assert-chr-effect ( chr -- )
    dup callable? [
        dup infer
        dup check-body-constraint-effect [ 2drop ] [ "invalid quot chr effect" 3array throw ] if
    ] [ drop ] if ;

: check-rule ( rule -- )
    [ guard>> ] [ body>> ] bi
    [ [ assert-chr-effect ] each ] bi@ ;

: add-rule ( program rule -- program )
    dup check-rule
    insert-existential-generators
    [ add-to-index ]
    [ [ suffix ] curry change-rules ]
    [ add-vars ] tri
    ;

: init-chr-prog ( rules -- prog )
    chr-prog new
    LH{ } clone >>occur-index
    LH{ } clone >>schedule
    swap [ add-rule ] each ;
