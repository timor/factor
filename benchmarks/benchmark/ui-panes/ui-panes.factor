USING: io kernel math.parser sequences ui.gadgets.panes ;
in: benchmark.ui-panes

: ui-panes-benchmark ( -- )
    [ 10000 iota [ number>string print ] each ] make-pane drop ;

main: ui-panes-benchmark
