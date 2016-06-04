USING: accessors stack-checker tools.test webapps.mason.report ;
in: webapps.mason.report.tests

! <build-report-action>
{ ( -- x ) } [
    <build-report-action> display>> infer
] unit-test
