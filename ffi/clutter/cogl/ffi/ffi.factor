! Copyright (C) 2010 Anton Gorenko.
! See http://factorcode.org/license.txt for BSD license.
USING: alien alien.libraries alien.syntax combinators
gobject-introspection kernel opengl.gl system vocabs ;
in: clutter.cogl.ffi

<<
"gobject.ffi" require
>>

library: clutter.cogl

<<
"clutter.cogl" {
    { [ os windows? ] [ drop ] }
    { [ os macosx? ] [ drop ] }
    { [ os unix? ] [ "libclutter-glx-1.0.so" cdecl add-library ] }
} cond
>>

FOREIGN-ATOMIc-type: GL.uint GLuint
FOREIGN-ATOMIc-type: GL.enum GLenum

gir: Cogl-1.0.gir
