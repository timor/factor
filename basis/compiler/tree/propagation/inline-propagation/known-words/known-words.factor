! Copyright (C) 2020 martinb.
! See http://factorcode.org/license.txt for BSD license.
USING: continuations continuations.private words ;
IN: compiler.tree.propagation.inline-propagation.known-words

\ dummy-1 t "never-propagate-inline" set-word-prop
\ dummy-2 t "never-propagate-inline" set-word-prop
! FIXME Taking this because it infers null, could be a general problem with null, though....
\ throw-restarts t "never-propagate-inline" set-word-prop
\ current-continuation t "never-propagate-inline" set-word-prop
