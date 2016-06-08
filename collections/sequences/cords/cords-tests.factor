USING: sequences.cords strings tools.test kernel sequences ;
in: sequences.cords.tests

{ "hello world" } [ "hello" " world" cord-append dup like ] unit-test
