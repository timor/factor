! Copyright (C) 2013 John Benediktsson
! See http://factorcode.org/license.txt for BSD license

USING: cocoa cocoa.application cocoa.classes kernel parser
multiline words ;

in: cocoa.apple-script

: run-apple-script ( str -- )
    [ NSAppleScript send\ alloc ] dip
    <NSString> send\ initWithSource: send\ autorelease
    f send\ executeAndReturnError: drop ;

SYNTAX: APPLESCRIPT:
    scan-new-word ";APPLESCRIPT" parse-multiline-string
    [ run-apple-script ] curry ( -- ) define-declared ;
