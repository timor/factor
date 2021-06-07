USING: help.markup help.syntax sequences ;

IN: combinators.sequential

HELP: with-prev*
{ $inputs { "quot" "a quotation that is applied to an element" } { "initial" "The initial value of " { $snippet "prev" } } }
{ $outputs { "quot" "a quotation that is applied to an element and it's last input " { $snippet "prev" } } }
{ $description "A combinator that modifies the input quotation to take another element below the top of stack.  This input element will be set to the value of " { $snippet "initial" } " on the first invocation of the quotation, and on subsequent invocations to the previous value of " { $snippet "elt" } "." } ;

HELP: +start+
{ $description { "A Singleton denoting the initial previous element for the " { $link with-prev } " combinator." } } ;

HELP: with-prev
{ $inputs { "quot" "a quotation that is applied to an element" } }
{ $outputs { "quot" "a quotation that is applied to an element and it's last input " { $snippet "prev" } } }
{ $description "A combinator that modifies the input quotation to take another element below the top of stack.  This input element will be set to the singleton " { $link +start+ } " on the first invocation of the quotation, and on subsequent invocations to the previous value of " { $snippet "elt" } "." }
{ $see-also reduce skip-start } ;

HELP: skip-start
{ $inputs { "quot" "a quotation that is applied to an element and it's predecessor " } { "default" "output of quotation instead of the first invocation" } }
{ $outputs { "quot" "a quotation that is applied to an element and it's predecessor " } }
{ $description "If this is used on a quotation before passing it to " { $link with-prev } ", the quotation is modified to be skipped on the initial invocation, instead returning " { $snippet "default" } " as quotation outputs (if any). " { $snippet "default" } " has no effect if the quotation does not produce any outputs (e.g. if it is passed to " { $link each } "). " } ;

HELP: with-next*
{ $inputs { "seq" sequence } { "quot" "a quotation that is applied to an element" } { "initial" "The initial value of " { $snippet "prev" } } }
{ $outputs { "seq" sequence } { "quot" "a quotation that is applied to an element and it's last input " { $snippet "prev" } } }
{ $description "A combinator that modifies the input quotation to be applied to successive elements of " { $snippet "seq" } ".  On the first invocation, " { $snippet "prev" } " will be set to the value of " { $snippet "initial" } ", and on subsequent invocations to the previous value of " { $snippet "elt" } ". Additionally, the quotation will be invoked one final time with the last element of the sequence and the singleton " { $link +end+ } " on top of stack." } ;

HELP: +end+
{ $description { "A Singleton denoting the final successor element for the " { $link with-next } " combinator." } } ;

HELP: with-next
{ $inputs { "seq" sequence } { "quot" "a quotation that is applied to an element" } }
{ $outputs { "seq" sequence } { "quot" "a quotation that is applied to an element and it's last input " { $snippet "prev" } } }
{ $description "A combinator that modifies the input quotation to be applied to successive elements of " { $snippet "seq" } ", which must have at least one element.  On invocations of the quotation, " { $snippet "prev" } " will be set to the first element of the sequence, and on subsequent invocations to the previous value of " { $snippet "elt" } ". Additionally, the quotation will be invoked one final time with the last element of the sequence and the singleton " { $link +end+ } " on top of stack." }
{ $see-also reduce skip-end } ;

HELP: skip-end
{ $inputs { "quot" "a quotation that is applied to an element and it's successor" } { "default" "output of quotation instead of the last invocation" } }
{ $outputs { "quot" "a quotation that is applied to an element and it's successor" } }
{ $description "If this is used on a quotation before passing it to " { $link with-next } ", the quotation is modified to be skipped on the final invocation, instead returning " { $snippet "default" } " as quotation outputs (if any). " { $snippet "default" } " has no effect if the quotation does not produce any outputs (e.g. if it is passed to " { $link each } "). " } ;

HELP: with-feedback
{ $inputs { "quot" "a quotation that is applied to an element and generates a next element" } { "elt0" "initial value of " { $snippet "eltN-1" } } }
{ $outputs { "quot" "a quotation that is applied to an element and the output of it's previous invocation" } }
{ $description "A combinator that modifies the input quotation to take the output of it's own last invocation as an additional input.  This is similar to " { $link accumulate } " and " { $link reduce } ", but can be used to create this kind of behavior compositionally when used with other combinators, and in contexts where the inputs are not sequences, or when it is tedious to keep track of intermediate elements on the stack." }
{ $examples
  { $example
    "USING: combinators.sequential kernel prettyprint sequences ;"
    "{ 2 2 2 2 2 } [ + ] 0 with-feedback map ."
    "{ 2 4 6 8 10 }"
  }
  { $example
    "USING: combinators.sequential kernel prettyprint sequences ;"
    "{ 2 2 2 2 2 } [ + + ] 0 with-feedback 0 with-feedback map ."
    "{ 2 6 14 30 62 }"
  }
  { $example
    "USING: combinators.sequential kernel prettyprint sequences ;"
    "{ 0 0 0 0 0 0 0 } [ + 0.5 * dup ] 1 with-feedback map ."
    "{ 0.5 0.25 0.125 0.0625 0.03125 0.015625 0.0078125 }"
  }
}
{ $see-also accumulate reduce } ;


ARTICLE: "combinators.sequential" "Sequential combinators"
"The words in the " { $vocab-link "combinators.sequential" } " vocabulary operate on quotations which remember inputs or outputs between calls using closure semantics.  The resulting quotations are stateful, where the state is initialized when the combinator is called." $nl
"General element-wise combinators:"
{  $subsections
   with-prev*
   with-prev
   skip-start
}
"Element-wise sequence combinators:"
{ $subsections
  with-next*
  with-next
  skip-end
}
"Call quotations with their own last output:"
{ $subsections
  with-feedback
} ;


ABOUT: "combinators.sequential"
