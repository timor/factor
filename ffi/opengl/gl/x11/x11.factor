USING: alien kernel x11.glx ;
in: opengl.gl.x11

: gl-function-context ( -- context ) glXGetCurrentContext ; inline
: gl-function-address ( name -- address ) glXGetProcAddressARB ; inline
: gl-function-calling-convention ( -- str ) cdecl ; inline
