USING: namespaces parser ;
in: vocabs.loader.test.a

COMPILE< global [ "count-me" inc ] with-variables COMPILE>

: v-l-t-a-hello ( -- a ) 4 ;

: byebye ( -- a ) v-l-t-a-hello ;

[ this is an error
