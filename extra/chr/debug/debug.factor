USING: accessors arrays assocs chr chr.state classes combinators formatting io
kernel namespaces prettyprint sequences tools.annotations ;

IN: chr.debug

: chr-state. ( -- )
    store get "Store: " print . ;

: chrebug ( -- )
    \ check/update-history [ [ 2dup "Rule %d match with match trace: %u\n" printf ] prepose ] annotate
    \ kill-chr [ [ dup "Killing id %d\n" printf  ] prepose ] annotate
    \ run-rule-body [ [ 2dup [ dup program get rules>> nth ] dip "Running Rule %d: %u\n with substitution:\n %u\n" printf ] prepose ] annotate
    \ activate-new [ [ dup "Activating new constraint: %u\n" printf ] prepose ] annotate
    \ activate [ [ chr-state. dup "Activating: %d\n" printf ] prepose ] annotate
    \ test-callable [ [ dup "Builtin Test: " write . ] prepose [ dup " ==> %u\n" printf ] compose ] annotate
    \ run-occurrence [ [ dup occurrence>> "Try Occurrence %u with Allowed Vars: " printf dup rule-vars>> . ] prepose ] annotate
    ;
