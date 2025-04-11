! Copyright (C) 2025 .
! See https://factorcode.org/license.txt for BSD license.
USING: help.markup help.syntax kernel quotations ;
IN: choose-fail

HELP: bf-choose
{ $values
    { "choices" object }
    { "item" object }
}
{ $description "" } ;

HELP: choose
{ $values
    { "choices" object }
    { "item" object }
}
{ $description "" } ;

HELP: choosing
{ $values
    { "quot1" quotation }
    { "quot2" quotation }
}
{ $description "" } ;

HELP: cut-all
{ $description "" } ;

HELP: cut-choice
{ $description "" } ;

HELP: fail
{ $description "" } ;

HELP: mark
{ $description "" } ;

HELP: no-more-choices
{ $description "Throws a " { $link no-more-choices } " error." }
{ $error-description "" } ;

HELP: not-in-choice-context
{ $description "Throws a " { $link not-in-choice-context } " error." }
{ $error-description "" } ;

HELP: with-choice
{ $values
    { "quot" quotation }
}
{ $description "" } ;

ARTICLE: "choose-fail" "choose-fail"
{ $vocab-link "choose-fail" }
;

ABOUT: "choose-fail"
