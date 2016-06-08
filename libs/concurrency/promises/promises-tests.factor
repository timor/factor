USING: vectors concurrency.promises kernel threads sequences
tools.test ;
in: concurrency.promises.tests

{ V{ 50 50 50 } } [
    0 <vector>
    <promise>
    [ ?promise swap push ] in-thread
    [ ?promise swap push ] in-thread
    [ ?promise swap push ] in-thread
    50 swap fulfill
] unit-test
