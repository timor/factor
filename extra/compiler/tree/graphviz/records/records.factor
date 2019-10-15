USING: accessors arrays circular classes.tuple colors.constants colors.hex
combinators formatting graphviz graphviz.notation kernel locals namespaces
sequences strings ;
IN: compiler.tree.graphviz.records

! * Records and Port Structures

SYMBOL: horizontal-layout
SYMBOL: color-record-edges

<PRIVATE
: escape-node-label ( str -- str )
    [ [ 1string ] [ "{}<>|" member? ] bi [ "\\" prepend ] when ]
    [ append ] map-reduce ;
PRIVATE>

TUPLE: port id label position ;

! Port id as used by graphviz
: port-id ( port -- str )
    [ id>> ] [ position>> "" or ] bi "%s%s" sprintf ;

: port-def ( port -- str )
    [ port-id ] [ label>> escape-node-label ] bi
    "<%s> %s" sprintf ;

: <port> ( id label -- port ) f port boa ;

! ** Record Node Protocol
! If an object implements these generics, it can be rendered as record nodes
GENERIC: input-ports ( obj -- ports )
GENERIC: output-ports ( obj -- ports )
GENERIC: record-title ( obj -- str )
GENERIC: record-info ( obj -- str/seq )
GENERIC: record-id ( obj -- id )


GENERIC: input-head-labels ( node -- seq )

! If this is implemented, the graph can be constructed completely assuming every
! input port has exactly one edge coming into it.
GENERIC#: input-port-source 1 ( node id -- node id )
GENERIC#: input-edge-label 1 ( node id -- str )

! ** Constructing the label

<PRIVATE

: in-curlies ( x -- x ) "{" "}" surround ;
PREDICATE: seq-sans-string < sequence string? not ;
: record ( seq -- str ) " | " join ;
: seq>record ( seq -- str )
    dup seq-sans-string?
    [ [ empty? ] reject [ seq>record ] map record in-curlies ]
    [ "%s" sprintf ] if ;
: (record-info) ( node -- str/f )
    record-info dup [ escape-node-label ] when ;

: assign-positions ( ports -- ports )
    [ >>position ] map-index ;

PRIVATE>

: <title-port> ( record -- port )
    record-title "title" swap <port> ;

: reverse-if-horizontal ( x -- x )
    horizontal-layout get [ reverse ] when ;

: (input-ports) ( x -- x )
    input-ports assign-positions ;

: record-label ( obj -- str )
    { [ <title-port> port-def ]
      [ (record-info) ]
      [ (input-ports) [ port-def ] map reverse-if-horizontal ]
      [ output-ports [ port-def ] map reverse-if-horizontal 2array ]
    } cleave
    3array 1array seq>record ;

: make-record-node ( record -- node )
    [ record-id <node> ] [ record-label =label ] bi
    "record" =shape ;

! ** User-visible Constructor
: <record-node> ( obj -- node )
    make-record-node ;

! ** Adding input edges if source-port is defined
! : port-ref ( node port -- str )
!     [ record-id ] [ port-id ] bi* "%s:%s" sprintf ;

:: output-port-by-id ( node id -- node port )
    node dup output-ports [ id>> id = ] find nip ;

: get-source-port ( node port -- node port )
    id>> input-port-source over
    [ output-port-by-id ]
    [ 2drop f f ] if ;

: set-tail-direction ( x x -- x )
    horizontal-layout get ":e" ":s" ? append =tailport ;

: set-head-direction ( x x -- x )
    horizontal-layout get ":w" ":n" ? append =headport ;

: edge-palette ( -- seq )
    { "base01" "yellow" "red" "violet" "cyan" "orange" "magenta" "blue" "green" }
    [ "solarized-" prepend named-color ] map <circular> ;

TUPLE: color-edge < edge ;
M: color-edge =color
    rgba>hex "#" prepend call-next-method ;

: <color-edge> ( tail head -- edge  )
    <edge> tuple-slots color-edge slots>tuple ;

: set-edge-color ( edge dest-port -- edge )
    position>> 0 or
    edge-palette nth =color ;

:: ported-edge ( n2 p2 n1 p1 -- edge )
    n1 n2 [ record-id ] bi@ <color-edge>
    p1 port-id set-tail-direction
    p2 port-id set-head-direction
    n2 p2 id>> input-edge-label =label
    color-record-edges get [ p2 set-edge-color ] when
    ;

: input-edge ( node port -- edge )
    2dup get-source-port
    [ ported-edge ]
    [ 3drop f ] if*
    ;

: input-edges ( node -- edges )
    [ dup (input-ports) [ input-edge ] with map ]
    [ input-head-labels ] bi
    [ [ =headlabel ] 2map ] when*
    ! drop
    ;
