USING: adsoda.combinators
sequences
    tools.test 
 ;

in: adsoda.combinators.tests


[ { "atoto" "b" "ctoto" } ] [ { "a" "b" "c" } 1 [ "toto" append ] map-but ] 
    unit-test

