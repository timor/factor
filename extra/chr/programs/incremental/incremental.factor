USING: accessors arrays assocs chr chr.programs kernel math sequences sets terms
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

:: add-heads ( program rule rule-ind entries -- program )
    entries <enumerated> >alist <reversed>
    [| hi ent |
     rule-ind hi 2array :> occ
     ent first2 :> ( aent partners )
     aent first2 :> ( hkept h )
     h constraint-type :> type
     occ type program occur-index>> push-at

     occ hkept h constraint-args partners rule match-vars>>
     <constraint-schedule>
     type program schedule>> push-at
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

: add-rule ( program rule -- program )
    insert-existential-generators
    [ add-to-index ]
    [ [ suffix ] curry change-rules ]
    [ add-vars ] tri
    ;

: init-chr-prog ( rules -- prog )
    chr-prog new
    H{ } clone >>occur-index
    H{ } clone >>schedule
    swap [ add-rule ] each ;
