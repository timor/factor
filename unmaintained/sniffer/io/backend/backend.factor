USING: io.backend kernel system vocabs.loader ;
in: io.sniffer.backend

symbol: sniffer-type
TUPLE: sniffer ;
HOOK: <sniffer> io-backend ( obj -- sniffer )
