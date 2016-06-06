! add each syntax word to core/bootstrap/syntax.factor
! scp boot.unix-x86.64.image.locals-and-roots slava_pestov@downloads.factorcode.org:downloads.factorcode.org/images/boot.unix-x86.64.image.locals-and-roots
! find . -type f -name '*.factor' -exec sed -i '' 's/\(^CALLBACK:.* (.*)\)/\1 ;/g' {} +
! lexable-core-paths [ dup . flush path>literals ] map-zip

"resource:language" vocabs-from
{ } diff
[ dup <vocab-link> . flush vocab>literals ] map-zip

"resource:collections" vocabs-from
{ 
} diff
[ dup <vocab-link> . flush vocab>literals ] map-zip

"resource:ffi" vocabs-from
{ "x11.syntax" "windows.com.syntax" "python.syntax" "opengl.gl.extensions"
 "opencl.syntax" "mongodb.tuple" "cuda.syntax" "core-foundation.strings"
 "cocoa.subclassing" "cocoa" "cocoa.apple-script" "gobject-introspection" } diff
[ dup <vocab-link> . flush vocab>literals ] map-zip

"resource:libs" vocabs-from
{ "annotations" "brainfuck" "dice" "infix" "logging"
"metar" "money" "poker" "qw" "roles" "roman" "slides"
"svg"  "urls" "xkcd" "calendar.holidays"
"calendar.holidays.canada" "calendar.holidays.us"
"colors.constants" "colors.hex" "gml.macros"
"gml.parser" "gml.runtime" "html.templates.chloe.syntax"
"infix.tokenizer" "irc.messages.base"
"math.complex" "math.rectangles" "math.blas.matrices"
"math.blas.vectors" "math.derivatives.syntax"
"math.vectors.simd" "math.vectors.simd.cords" "peg.pl0"
"peg.javascript.parser" "peg.javascript.tokenizer"
"unicode.categories" "units.reduction" "xml.errors"
"xml.syntax" "xmode.loader.syntax" "yaml.conversion"
} diff
[ dup <vocab-link> . flush vocab>literals ] map-zip

"resource:frameworks" vocabs-from
{ "ui.theme.switching" "ui.backend.cocoa.views" "ui.backend.cocoa.tools"
"ui.backend.gtk" "ui.backend.cocoa" "gpu.demos.raytrace" "gpu.demos.bunny"
"gpu.shaders" "gpu.render" "game.worlds" "ui" "db.postgresql.errors" } diff
[ dup <vocab-link>  . flush vocab>literals ] map-zip

"resource:tools" vocabs-from
{ "help.syntax" "help.tips" "tools.test" "tools.walker"
"vocabs.git" } diff
[ dup <vocab-link> . flush vocab>literals ] map-zip

"resource:demos" vocabs-from
{ "talks.vpri-talk" "talks.tc-lisp-talk" "talks.minneapolis-talk" "talks.google-tech-talk"
 "talks.galois-talk" "talks.otug-talk" "smalltalk.selectors" "smalltalk.parser"
 "smalltalk.library" "bunny.outlined" "project-euler.common" } diff
[ dup <vocab-link>  . flush vocab>literals ] map-zip

in: syntax

USING: classes.tuple.parser classes.builtin ;

SYNTAX: in: scan-token set-current-vocab ;
SYNTAX: use: scan-token use-vocab ;
SYNTAX: unuse: scan-token unuse-vocab ;
SYNTAX: postpone\ scan-word suffix! ;
SYNTAX: postpone\ scan-word suffix! ;

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

SYNTAX: POSTPONE\ scan-word suffix! ;
SYNTAX: postpone\ scan-word suffix! ;
