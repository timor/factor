! Copyright (C) 2016 Doug Coleman.
! See http://factorcode.org/license.txt for BSD license.
USING: accessors kernel modern sequences strings tools.test ;
in: modern.tests

{ 0 } [ "" string>literals length ] unit-test
{ 1 } [ "a" string>literals length ] unit-test
{ 1 } [ " a" string>literals length ] unit-test
{ 1 } [ " a " string>literals length ] unit-test
{ 3 } [ "a b c" string>literals length ] unit-test

{ 1 } [ "`abc" string>literals length ] unit-test
{ 2 } [ "`abc `cba" string>literals length ] unit-test
{ 2 } [ "\"abc\" \"cba\"" string>literals length ] unit-test
{ 2 } [ "[[abc]] [[cba]]" string>literals length ] unit-test
{ 2 } [ "{{abc}} {{cba}}" string>literals length ] unit-test
{ 2 } [ "((abc)) ((cba))" string>literals length ] unit-test
{ 2 } [ "[=[abc]=] [=[cba]=]" string>literals length ] unit-test
{ 2 } [ "{={abc}=} {={cba}=}" string>literals length ] unit-test
{ 2 } [ "(=(abc)=) (=(cba)=)" string>literals length ] unit-test
{ 2 } [ "[==[abc]==] [==[cba]==]" string>literals length ] unit-test
{ 2 } [ "{=={abc}==} {=={cba}==}" string>literals length ] unit-test
{ 2 } [ "(==(abc)==) (==(cba)==)" string>literals length ] unit-test

: literal-test ( string -- n string string string )
    string>literals [ length ] [ first [ tag>> ] [ delimiter>> ] [ payload>> ] tri ] bi ;

{ 1 "hex" "`" "abc" } [ "hex`abc" literal-test ] unit-test
{ 2 "hex" "`" "abc" } [ "hex`abc hex`cba" literal-test ] unit-test
{ 2 "hex" "\"" "abc" } [ "hex\"abc\" hex\"cba\"" literal-test ] unit-test
{ 2 "hex" "[[" "abc" } [ "hex[[abc]] hex[[cba]]" literal-test ] unit-test
{ 2 "hex" "{{" "abc" } [ "hex{{abc}} hex{{cba}}" literal-test ] unit-test
{ 2 "hex" "((" "abc" } [ "hex((abc)) hex((cba))" literal-test ] unit-test
{ 2 "hex" "[=[" "abc" } [ "hex[=[abc]=] hex[=[cba]=]" literal-test ] unit-test
{ 2 "hex" "{={" "abc" } [ "hex{={abc}=} hex{={cba}=}" literal-test ] unit-test
{ 2 "hex" "(=(" "abc" } [ "hex(=(abc)=) hex(=(cba)=)" literal-test ] unit-test
{ 2 "hex" "[==[" "abc" } [ "hex[==[abc]==] hex[==[cba]==]" literal-test ] unit-test
{ 2 "hex" "{=={" "abc" } [ "hex{=={abc}==} hex{=={cba}==}" literal-test ] unit-test
{ 2 "hex" "(==(" "abc" } [ "hex(==(abc)==) hex(==(cba)==)" literal-test ] unit-test


{ 1 } [ "[ ]" string>literals length ] unit-test
{ 1 } [ "abc[ ]" string>literals length ] unit-test
{ 1 } [ "abc[ 1 ]" string>literals length ] unit-test
{ 1 } [ "abc[ 1 abc]" string>literals length ] unit-test
{ 1 } [ "{ }" string>literals length ] unit-test
{ 1 } [ "abc{ }" string>literals length ] unit-test
{ 1 } [ "abc{ 1 }" string>literals length ] unit-test
{ 1 } [ "abc{ 1 abc}" string>literals length ] unit-test

{ 1 } [ "( )" string>literals length ] unit-test
{ 1 } [ "abc( )" string>literals length ] unit-test
{ 1 } [ "abc( 1 )" string>literals length ] unit-test
{ 1 } [ "abc( 1 abc)" string>literals length ] unit-test

[ "A{ B}" string>literals ] must-fail
[ "A( B)" string>literals ] must-fail
[ "A[ B]" string>literals ] must-fail
[ "A: B;" string>literals ] must-fail
[ "A: AA;" string>literals ] must-fail
[ "A: B{ C} A;" string>literals ] must-fail

{ 1 } [ "!omg" string>literals length ] unit-test
{ 1 } [ "! omg" string>literals length ] unit-test
{ 1 } [ "![[omg]]" string>literals length ] unit-test
{ 1 } [ "![[
    omg]]" string>literals length
] unit-test

{ 1 } [ "\\ a" string>literals length ] unit-test
{ 1 } [ "\\ \\" string>literals length ] unit-test
{ 1 } [ " \\   abcd " string>literals length ] unit-test

{ "omg" } [ "!omg" string>literals first payload>> >string ] unit-test

! Comment character should be #, and should not be allowed in word names
! For now, we have exclamation as comment character and words
! like suffix! which aren't allowed to start comments
{ 2 } [ "a!omg lol" string>literals length ] unit-test
{ 3 } [ "a! omg lol" string>literals length ] unit-test
{ 2 } [ "a![[omg]] lol" string>literals length ] unit-test

{ t } [ "[ ][ ][ ]" string>literals length 1 = ] unit-test
{ t } [ "[ ][ ][ ]" string>literals first compound-literal? ] unit-test
{ t } [ "[ ][ ][ ]" string>literals first sequence>> length 3 = ] unit-test

! This is broken.
! hex[[abc]] -> hex#[[abc]] ! commented out hex literal!
! $hex[[abc${0}]]           ! interpolate
! { 2 } [ "a![[
!    omg]] lol" string>literals length
! ] unit-test

! Disabled right decorators for now
! { 1 } [ "a@ b@ hi @c @d" string>literals length ] unit-test

! Disabled right decorators for now
! { 1 } [ "{ 1 }@ { 2 }@ hi @{ 3 } @{ 4 }" string>literals length ] unit-test


{ 1 } [ ":foo" string>literals length ] unit-test
{ 1 } [ "( :integer )" string>literals length ] unit-test


{ 1 } [ "postpone\\ main:" string>literals length ] unit-test
{ 1 } [ "char: \\!" string>literals length ] unit-test
