! Copyright (C) 2010 Anton Gorenko.
! See http://factorcode.org/license.txt for BSD license.
USING: alien alien.libraries alien.syntax combinators
gobject-introspection kernel system vocabs ;
IN: atk.ffi

COMPILE< "gobject.ffi" require COMPILE>

LIBRARY: atk

COMPILE< "atk" {
    { [ os windows? ] [ "libatk-1.0-0.dll" ] }
    { [ os macosx? ] [ "libatk-1.0.dylib" ] }
    { [ os unix? ] [ "libatk-1.0.so" ] }
} cond cdecl add-library COMPILE>

gir: vocab:atk/Atk-1.0.gir
