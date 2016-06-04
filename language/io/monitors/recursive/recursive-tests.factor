USING: accessors math kernel namespaces continuations
io.files io.monitors io.monitors.recursive io.backend
concurrency.mailboxes tools.test destructors io.files.info
io.pathnames io.files.temp io.directories.hierarchy fry ;
in: io.monitors.recursive.tests

singleton: mock-io-backend

TUPLE: mock-counter i ;

symbol: dummy-monitor-created
symbol: dummy-monitor-disposed

TUPLE: dummy-monitor < monitor ;

M: dummy-monitor dispose*
    drop dummy-monitor-disposed get [ 1 + ] change-i drop ;

M: mock-io-backend (monitor)
    nip
    over exists? [
        dummy-monitor new-monitor
        dummy-monitor-created get [ 1 + ] change-i drop
    ] [
        "Does not exist" throw
    ] if ;

M: mock-io-backend link-info
    global [ link-info ] with-variables ;

{ } [ 0 mock-counter boa dummy-monitor-created set ] unit-test
{ } [ 0 mock-counter boa dummy-monitor-disposed set ] unit-test

{ } [
    mock-io-backend io-backend [
        "resource:core/io" resource-path <mailbox> <recursive-monitor> dispose
    ] with-variable
] unit-test

{ t } [ dummy-monitor-created get i>> 0 > ] unit-test

{ t } [ dummy-monitor-created get i>> dummy-monitor-disposed get i>> = ] unit-test

[ "doesnotexist" temp-file delete-tree ] ignore-errors

[
    0 mock-counter boa dummy-monitor-created [
        mock-io-backend io-backend [
            "doesnotexist" temp-file <mailbox> <recursive-monitor> dispose
        ] with-variable
    ] with-variable
] must-fail

{ } [ 0 mock-counter boa dummy-monitor-created set ] unit-test
{ } [ 0 mock-counter boa dummy-monitor-disposed set ] unit-test

! Test that disposing twice is allowed
{ } [
    "resource:core/io" resource-path <mailbox> <recursive-monitor>
    [ dispose ] [ dispose ] bi
] unit-test
