USING: accessors compiler.tree compiler.tree.builder compiler.tree.cleanup
compiler.tree.combinators compiler.tree.dead-code compiler.tree.def-use
compiler.tree.eliminate-renaming compiler.tree.escape-analysis
compiler.tree.escape-analysis.check compiler.tree.graphviz.edges
compiler.tree.graphviz.nodes compiler.tree.graphviz.records
compiler.tree.graphviz.variables compiler.tree.identities
compiler.tree.modular-arithmetic compiler.tree.normalization
compiler.tree.optimizer compiler.tree.propagation compiler.tree.recursive
compiler.tree.tuple-unboxing compiler.tree.value-infos graphviz
graphviz.notation graphviz.render images.viewer io.files.temp io.pathnames
kernel namespaces sequences typed ui ui.gadgets.scrollers words ;

IN: compiler.tree.graphviz

USE: compiler.tree.propagation.info.present

FROM: compiler.tree => node node? ;
FROM: namespaces => set ;

! * Graphviz visualization


! ** Building Trees for Visualization

! Use this to make a tree if no particular tree is provided
! This is just the regular frontend optimization skipping the finalization step.
: maybe-eliminate-shuffles ( nodes -- nodes' )
    keep-shuffle-nodes get [ eliminate-renaming ] unless ;

: treeviz-tree ( word/quot -- nodes )
    build-tree
    [
        analyze-recursive
        normalize
        propagate
        cleanup-tree
        dup run-escape-analysis? [
            escape-analysis
            unbox-tuples
        ] when
        apply-identities
        compute-def-use
        remove-dead-code
        ?check
        compute-def-use
        optimize-modular-arithmetic
    ] with-scope ;

! ** Generating the graph

: treeviz ( nodes -- graph )
    [
        <digraph>
        horizontal-layout get "LR" "TB" ? =rankdir
        swap
        [
            [
                [ add-tree-node ]
                [ add-input-edges ]
                bi
            ] each-node
        ] keep
        hide-control-edges get [ drop ] [
            push-nodes-as-control get [
                [ dup #push? [ drop f ] when ] map-nodes
            ] unless
            add-edges-between
        ] if
    ] with-tree-value-infos
    ;

: show-graph ( graph -- )
    [ [
        "preview" png
        "preview.png" <image-gadget> <scroller> "CDFG" open-window
    ] with-temp-directory ] curry with-ui ;

: treeviz. ( nodes -- )
    maybe-eliminate-shuffles treeviz show-graph ;

: actual-def ( word -- code )
    dup typed-word? [ "typed-word" word-prop ] when ;

: quot>cdfg ( word/quot -- graph )
    actual-def treeviz-tree treeviz ;

: cdfg. ( word/quot -- ) quot>cdfg show-graph ;

UNION: non-dfg-node #terminate #return-recursive ;

: dfgviz ( nodes -- graph )
    H{ { hide-control-edges t }
       { horizontal-layout t }
       { show-muxes f }
       { color-record-edges t }
    } [
        maybe-eliminate-shuffles
        [ dup non-dfg-node? [ drop f ] when ] map-nodes
        show-muxes get [ phi>mux ] when
        treeviz
    ] with-variables ;

: quot>dfg ( word/quot -- graph )
    actual-def treeviz-tree dfgviz ;

: dfgviz. ( nodes -- )
    dfgviz show-graph ;

: dfg. ( word/quot -- ) quot>dfg show-graph ;

: write-dfg ( filename word/quot -- )
    quot>dfg
    swap "-dfg" append
    [ dot-file ] [ png ] [ svg ] 2tri ;

: write-cdfg ( filename word/quot -- )
    quot>cdfg
    swap "-cdfg" append
    [ dot-file ] [ png ] [ svg ] 2tri ;

SYMBOL: graph-output-path
ERROR: no-output-path-set ;

: quot>graphs ( quot name -- )
    graph-output-path get
    [
        swap append-path swap
        [ write-dfg ]
        [ write-cdfg ] 2bi
    ]
    [ drop no-output-path-set ] if* ;

: save-word-graphs ( word -- )
    dup name>> quot>graphs ;
