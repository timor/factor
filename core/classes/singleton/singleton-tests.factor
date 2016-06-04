USING: classes.singleton io.streams.string kernel see tools.test ;
in: classes.singleton.tests

{ } [ singleton: bzzt ] unit-test
{ t } [ bzzt bzzt? ] unit-test
{ t } [ bzzt bzzt eq? ] unit-test
GENERIC: zammo ( obj -- str ) ;
{ } [ M: bzzt zammo drop "yes!" ; ] unit-test
{ "yes!" } [ bzzt zammo ] unit-test
{ } [ singleton: omg ] unit-test
{ t } [ omg singleton-class? ] unit-test
{ "in: classes.singleton.tests\nsingleton: omg\n" } [ [ omg see ] with-string-writer ] unit-test

singleton: word-and-singleton

: word-and-singleton ( -- x ) 3 ;

{ t } [ \ word-and-singleton word-and-singleton? ] unit-test
{ 3 } [ word-and-singleton ] unit-test
