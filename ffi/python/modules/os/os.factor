USING: python.syntax ;
in: python.modules.os

PY-FROM: os =>
    getpid ( -- y )
    system ( x -- y ) ;
