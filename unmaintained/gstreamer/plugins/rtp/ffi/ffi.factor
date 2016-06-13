! Copyright (C) 2010 Anton Gorenko.
! See http://factorcode.org/license.txt for BSD license.
USING: alien alien.libraries combinators kernel system
gobject-introspection glib.ffi gstreamer.base.ffi gstreamer.ffi ;
in: gstreamer.rtp.ffi

COMPILE<
"gstreamer.rtp" {
    { [ os winnt? ] [ drop ] }
    { [ os macosx? ] [ drop ] }
    { [ os unix? ] [ "libgstrtp-0.10.so" cdecl add-library ] }
} cond
COMPILE>

gir: vocab:gstreamer/rtp/GstRtp-0.10.gir

