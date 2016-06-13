! Copyright (C) 2010 Anton Gorenko.
! See http://factorcode.org/license.txt for BSD license.
USING: alien alien.c-types alien.libraries combinators kernel
system
gobject-introspection glib.ffi gstreamer.ffi gstreamer.base.ffi
gstreamer.interfaces.ffi ;
in: gstreamer.audio.ffi

COMPILE<
"gstreamer.audio" {
    { [ os winnt? ] [ drop ] }
    { [ os macosx? ] [ drop ] }
    { [ os unix? ] [ "libgstaudio-0.10.so" cdecl add-library ] }
} cond
COMPILE>

gir: vocab:gstreamer/audio/GstAudio-0.10.gir

