USING: tools.test xml.writer ;
in: webapps.mason.downloads

{ "<p>No machines.</p>" } [
    { } builder-list xml>string
] unit-test
