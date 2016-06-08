USING: python.syntax ;
in: python.modules.sys

PY-FROM: sys =>
    path ( -- seq )
    argv ( -- seq )
    getrefcount ( obj -- n )
    platform ( -- x ) ;
