USING: formatting io kernel namespaces prettyprint sequences tools.annotations
types.inference ;

IN: types.debug

: type-state. ( -- )
    quot-done get
    quot-todo get "%s | %s" printf ;

: (type-step.) ( stack word tword -- stack word )
    nl "========= %s " printf
    2dup . . type-state. nl ;

: (forward.) ( stack tword -- stack )
    nl "====== %s " printf type-state. nl ;

! Should work on quotations that have stack and word on input
: annotate-type-step ( word -- )
    dup '[ [ _ (type-step.) ] prepose ] annotate ;


: tebug ( -- )
    { do-word undo-word apply-inputs } [ annotate-type-step ] each
    \ rewind watch
    \ forward dup '[ [ _ (forward.) ] prepose ] annotate
    \ ?transform-word watch
    ;
