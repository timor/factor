! Copyright (C) 2010 Anton Gorenko.
! See http://factorcode.org/license.txt for BSD license.
USING: alien alien.libraries alien.syntax combinators
gobject-introspection kernel system vocabs ;
IN: clutter.json.ffi

COMPILE<
"gobject.ffi" require
"gio.ffi" require
COMPILE>

LIBRARY: clutter.json

COMPILE<
"clutter.json" {
    { [ os windows? ] [ drop ] }
    { [ os macosx? ] [ drop ] }
    { [ os unix? ] [ "libclutter-glx-1.0.so" cdecl add-library ] }
} cond
COMPILE>

GIR: Json-1.0.gir
