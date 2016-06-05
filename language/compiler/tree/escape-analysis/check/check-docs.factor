USING: help.markup help.syntax kernel sequences ;
in: compiler.tree.escape-analysis.check

HELP: run-escape-analysis?
{ $values { "nodes" sequence } { "?" boolean } }
{ $description "Whether to run escape analysis on the nodes or not." } ;

ARTICLE: "compiler.tree.escape-analysis.check"
"Skipping escape analysis pass for code which does not allocate" ;

about: "compiler.tree.escape-analysis.check"
