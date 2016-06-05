! add each syntax word to core/bootstrap/syntax.factor
! scp boot.unix-x86.64.image.locals-and-roots slava_pestov@downloads.factorcode.org:downloads.factorcode.org/images/boot.unix-x86.64.image.locals-and-roots
! find . -type f -name '*.factor' -exec sed -i '' 's/\(^CALLBACK:.* (.*)\)/\1 ;/g' {} +
! lexable-core-paths [ dup . flush path>literals ] map-zip

"resource:ffi" vocabs-from
{ "cocoa.dialogs" "opengl.gl.extensions" "python.syntax"
"windows.com.syntax" "x11.syntax"
"cocoa.application" "opencl.syntax" "mongodb.tuple" "cuda.syntax" "core-foundation.strings" 
"cocoa.windows" "cocoa.views" "cocoa.subclassing" 
"cocoa.nibs" "cocoa.plists" "cocoa" "cocoa.messages"
 "gobject-introspection" "cocoa.apple-script" } diff
[ dup . flush vocab>literals ] map-zip

"resource:language" vocabs-from
{ "constructors" "descriptive" "eval" "functors" "literals"
"match" "method-chains" "multi-methods" "multiline"
"pair-methods" "peg" "promises" "shuffle" "tr" "tuple-arrays"
"variables" "variants" "alien.data" "alien.endian" "alien.fortran"
"alien.syntax" "alien.data.map" "classes.struct"
"classes.struct.vectored" "compiler.codegen" "functors.backend"
"compiler.cfg.dataflow-analysis" "compiler.cfg.renaming.functor"
"compiler.cfg.registers" "cpu.8080.emulator" "definitions.icons"
"compiler.cfg.instructions.syntax" "cpu.x86.assembler.syntax"
"io.encodings.euc" "peg.ebnf" "prettyprint.stylesheet" "slots.syntax"
 } diff
[ dup . flush vocab>literals ] map-zip

"resource:frameworks" vocabs-from
{ "ui.theme.switching" "ui.backend.cocoa.views" "ui.backend.cocoa.tools"
"ui.backend.gtk" "ui.backend.cocoa" "gpu.demos.raytrace" "gpu.demos.bunny"
"gpu.shaders" "gpu.render" "game.worlds" "ui" "db.postgresql.errors" } diff
[ dup . flush vocab>literals ] map-zip

"resource:demos" vocabs-from
{  "talks.vpri-talk" "talks.tc-lisp-talk" "talks.minneapolis-talk" "talks.google-tech-talk"
 "talks.galois-talk" "talks.otug-talk" "smalltalk.selectors" "smalltalk.parser"
 "smalltalk.library" "webkit-demo" "bunny.outlined" "project-euler.common" } diff
[ dup . flush vocab>literals ] map-zip

in: syntax

USING: classes.tuple.parser classes.builtin ;

SYNTAX: in: scan-token set-current-vocab ;
SYNTAX: use: scan-token use-vocab ;
SYNTAX: unuse: scan-token unuse-vocab ;
SYNTAX: postpone: scan-word suffix! ;
SYNTAX: postpone: scan-word suffix! ;

SYNTAX: @inline last-word make-inline ;
SYNTAX: @recursive last-word make-recursive ;
SYNTAX: @foldable last-word make-foldable ;
SYNTAX: @flushable last-word make-flushable ;
SYNTAX: @delimiter last-word t "delimiter" set-word-prop ;
SYNTAX: @deprecated last-word make-deprecated ;
SYNTAX: @final last-word make-final ;

SYNTAX: symbol: scan-new-word define-symbol ;
SYNTAX: singleton: scan-new-class define-singleton-class ;
SYNTAX: mixin: scan-new-class define-mixin-class ;

SYNTAX: forget: scan-object forget ;

SYNTAX: main:
    scan-word dup ( -- ) check-stack-effect
    [ current-vocab main<< ]
    [ current-source-file get [ main<< ] [ drop ] if* ] bi ;

SYNTAX: nan: 16 scan-base <fp-nan> suffix! ;

SYNTAX: char:
    lexer get parse-raw [ "token" throw-unexpected-eof ] unless* 
    {
        { [ dup length 1 = ] [ first ] }
        { [ "\\" ?head ] [ next-escape >string "" assert= ] }
        [ name>char-hook get ( name -- char ) call-effect ]
    } cond suffix! ;

SYNTAX: defer:
    scan-token current-vocab create-word
    [ fake-definition ] [ set-last-word ]
    [ undefined-def define ] tri ;

SYNTAX: PRIMITIVE:
    current-vocab name>> scan-word scan-effect ";" expect ensure-primitive ;


SYNTAX: CONSTANT: scan-new-word scan-object ";" expect define-constant ;

SYNTAX: qualified: scan-token dup add-qualified ;

SYNTAX: QUALIFIED-WITH: scan-token scan-token ";" expect add-qualified ;
