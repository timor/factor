! Copyright (C) 2010 Anton Gorenko.
! See http://factorcode.org/license.txt for BSD license.
USING: alien alien.libraries alien.syntax cairo.ffi combinators
gobject-introspection kernel system vocabs ;
IN: clutter.ffi

COMPILE<
"gtk" require
"atk.ffi" require
"pango.cairo.ffi" require
"clutter.cogl.ffi" require
"clutter.json.ffi" require
COMPILE>

LIBRARY: clutter

COMPILE<
"clutter" {
    { [ os windows? ] [ drop ] }
    { [ os macosx? ] [ drop ] }
    { [ os unix? ] [ "libclutter-glx-1.0.so" cdecl add-library ] }
} cond
COMPILE>

FOREIGN-RECORD-TYPE: cairo.Path cairo_path_t

GIR: Clutter-1.0.gir
