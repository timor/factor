in: tools.deploy.test.2
USING: calendar calendar.format ;

: deploy-test-2 ( -- ) now (timestamp>string) ;

main: deploy-test-2
