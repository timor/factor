USING: http.server.static tools.test xml.writer ;
in: http.server.static.tests

{ } [ "resource:basis" directory>html write-xml ] unit-test
