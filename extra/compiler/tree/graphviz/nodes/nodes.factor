USING: accessors classes compiler.tree compiler.tree.eliminate-renaming
compiler.tree.graphviz.records compiler.tree.value-infos effects formatting
graphviz graphviz.notation io.streams.string kernel namespaces prettyprint
prettyprint.config sequences words ;

IN: compiler.tree.graphviz.nodes

FROM: compiler.tree => node node? ;

! * Node handling
! Connectivity information relies on the context created by with-tree-value-infos.

! Nodes involved in recursive control flow:
UNION: recursive-node #recursive #call-recursive #return-recursive ;

! Nodes which are ignored during control flow:
! UNION: data-node #shuffle #copy #push ;

! ** Node Rendering
! Return the ID which graphviz uses internally to identify the nodes
M: object record-id [ class-of name>> ] [ identity-hashcode ] bi "%s(%x)" sprintf ;

! Called after a dot vertex has been created for node.
GENERIC: set-node-attributes* ( attrs node -- attrs )

! For gensyms representing undefined
M: word set-node-attributes* drop "plain" =shape ;
M: object set-node-attributes* drop ;

! Return the string which constitutes the node's label
GENERIC: node-label ( vertex -- str )

! For gensyms representing undefined
M: word node-label drop "?" ;

! ** Printing Literals
! Return the representation of factor literals which is supposed to be used in labels
GENERIC: literal-label ( obj -- str )

! M: tuple vertex-id call-next-method ;

M: object literal-label
    H{
        { margin 12 }
        { line-limit 4 }
        { nesting-limit 2 }
        { length-limit 3 }
    } [ [ pprint-short ] with-string-writer ] with-variables ;

! ** Record Shapes for Tree Nodes
! Record shape labels contain 4 elements in their structure: The node type, the input ports, the
! output ports, and the internal information

M: node record-title ( node -- str ) class-of name>> ;


! While output ports can be identified by value only, input ports get their position coded into the id as well.

! ** Ports

<PRIVATE
: value-ports ( values prefix -- ports )
    swap [ "%s%d" sprintf <port> ] with map-index ;
PRIVATE>

! Return a list of input ports to render
M: node input-ports
    in-d>> "d" value-ports ;

M: #shuffle input-ports
    [ in-d>> "d" value-ports ]
    [ in-r>> "r" value-ports ] bi
    append ;

M: #call input-ports
    [ in-d>> ] keep word>> stack-effect in>>
    [ effect>string <port> ] 2map ;

M: #phi input-ports
     phi-in-d>> first2
    [ "t" value-ports ]
    [ "f" value-ports ] bi* append ;

! #mux pseudo-nodes
M: #mux input-ports
    [ call-next-method ] keep
    in-d>> "phi" value-ports append ;

M: no-data-in-node input-ports drop { } ;

! Return a list of output ports to render
M: node output-ports
    out-d>> "d" value-ports ;
M: #shuffle output-ports
    [ out-d>> "d" value-ports ] [ out-r>> "r" value-ports ] bi append ;
M: non-def-node output-ports drop { } ;

M: #call output-ports
    [ out-d>> ] keep word>> stack-effect out>>
    [ effect>string <port> ] 2map ;

! Return a string describing the node specifics
M: node record-info drop f ;
M: #call record-info word>> name>> ;
M: #push record-info literal>> literal-label ;

! ** Adding nodes
GENERIC: add-simple-tree-node ( graph node -- graph )
: make-node ( node -- graph-node node )
    [ record-id <node> "rect" =shape ] keep ;

M: node add-simple-tree-node
    make-node class-of name>> =label add ;
M: #push add-simple-tree-node
    make-node literal>> literal-label =label
    "plain" =shape add ;
M: #call add-simple-tree-node
    make-node word>> name>> =label add ;
M: #introduce add-simple-tree-node
    <record-node> add ;
M: #return add-simple-tree-node
    <record-node> add ;
M: #mux add-simple-tree-node
    make-node drop
    "" =label
    horizontal-layout get [ "90" =orientation ] when
    "invtrapezium" =shape add ;

GENERIC: add-tree-node ( graph node -- graph )
M: node add-tree-node
    simple-graph get
    [ add-simple-tree-node ]
    [ <record-node> add ] if ;

M: #if add-tree-node
    show-muxes get
    [ drop ]
    [ call-next-method ] if ;

M: #push add-tree-node
    push-nodes-as-control get
    [ call-next-method ]
    [
        make-node literal>> literal-label =label
        "oval" =shape
        add
    ] if ;

