USING: namespaces ;
in: vocabs.loader.test.b

COMPILE< global [ "count-me" inc ] with-variables COMPILE>

: fred ( -- ) bob ;
