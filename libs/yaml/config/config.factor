! Copyright (C) 2014 Jon Harper.
! See http://factorcode.org/license.txt for BSD license.
USING: kernel namespaces sequences ;
IN: yaml.config

! Configuration
! The following are libyaml's emitter configuration options
symbol: emitter-canonical
symbol: emitter-indent
symbol: emitter-width
symbol: emitter-unicode
symbol: emitter-line-break

! Set this value to keep libyaml's default
symbol: +libyaml-default+

{
    emitter-canonical
    emitter-indent
    emitter-width
    emitter-line-break
} [ +libyaml-default+ swap set-global ] each
! But Factor is unicode-friendly by default
t emitter-unicode set-global

symbol: implicit-tags
t implicit-tags set-global

symbol: implicit-start
symbol: implicit-end
t implicit-start set-global
t implicit-end set-global

! By default, give the simplest representation of the document
symbol: merge
symbol: value
t merge set-global
t value set-global
