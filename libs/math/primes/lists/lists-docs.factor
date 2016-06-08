USING: help.markup help.syntax math ;
in: math.primes.lists

HELP: lprimes
{ $values { "list" "a lazy list" } }
{ $description "Return a sorted list containing all the prime numbers." } ;

HELP: lprimes-from
{ $values { "n" integer } { "list" "a lazy list" } }
{ $description "Return a sorted list containing all the prime numbers greater or equal to " { $snippet "n" } "." } ;
