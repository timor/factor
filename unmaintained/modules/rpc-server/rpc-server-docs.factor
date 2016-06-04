USING: help.syntax help.markup modules.rpc-server modules.using ;
in: modules.rpc-server
HELP: service
{ $syntax "in: my-vocab service" }
{ $description "Allows words defined in the vocabulary to be used as remote procedure calls by " { $link postpone: USING*: } } ;
