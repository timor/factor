! Copyright (C) 2005, 2009 Slava Pestov.
! See http://factorcode.org/license.txt for BSD license.
USING: accessors arrays compiler.units definitions help
help.markup help.topics kernel lexer math parser quotations
sequences vocabs.parser words splitting ;
IN: help.syntax

SYNTAX: \ HELP:
    scan-escaped-word bootstrap-word
    [ >link save-location ]
    [ [ \ ; parse-until >array ] dip set-word-help ]
    bi ;

ERROR: article-expects-name-and-title got ;

SYNTAX: \ ARTICLE:
    location [
        \ ; parse-until >array
        dup length 2 < [ article-expects-name-and-title ] when
        [ first2 ] [ 2 tail ] bi <article>
        over add-article >link
    ] dip remember-definition ;

SYNTAX: \ ABOUT:
    current-vocab scan-object >>help changed-definition ;

COMPILE<
SYNTAX: \ HELP-SYNTAX:
    scan-new-escaped scan-word ";" expect
    '[ \ } parse-until split-dashes >array _ prefix suffix! ] define-syntax ;
COMPILE>

HELP-SYNTAX: \ $breadcrumbs{ $breadcrumbs ;
HELP-SYNTAX: \ $class-description{ $class-description ;
HELP-SYNTAX: \ $code{ $code ;
HELP-SYNTAX: \ $complex-shuffle{ $complex-shuffle ;
HELP-SYNTAX: \ $content{ $content ;
HELP-SYNTAX: \ $contract{ $contract ;
HELP-SYNTAX: \ $curious{ $curious ;
HELP-SYNTAX: \ $definition{ $definition ;
HELP-SYNTAX: \ $definition-icons{ $definition-icons ;
HELP-SYNTAX: \ $deprecated{ $deprecated ;
HELP-SYNTAX: \ $description{ $description ;
HELP-SYNTAX: \ $emphasis{ $emphasis ;
HELP-SYNTAX: \ $error-description{ $error-description ;
HELP-SYNTAX: \ $errors{ $errors ;
HELP-SYNTAX: \ $example{ $example ;
HELP-SYNTAX: \ $examples{ $examples ;
HELP-SYNTAX: \ $heading{ $heading ;
HELP-SYNTAX: \ $image{ $image ;
HELP-SYNTAX: \ $instance{ $instance ;
HELP-SYNTAX: \ $io-error{ $io-error ;
HELP-SYNTAX: \ $link{ $link ;
HELP-SYNTAX: \ $links{ $links ;
HELP-SYNTAX: \ $list{ $list ;
HELP-SYNTAX: \ $long-link{ $long-link ;
HELP-SYNTAX: \ $low-level-note{ $low-level-note ;
HELP-SYNTAX: \ $markup-example{ $markup-example ;
HELP-SYNTAX: \ $maybe{ $maybe ;
HELP-SYNTAX: \ $methods{ $methods ;
HELP-SYNTAX: \ $nl{ $nl ;
HELP-SYNTAX: \ $notes{ $notes ;
HELP-SYNTAX: \ $or{ $or ;
HELP-SYNTAX: \ $parsing-note{ $parsing-note ;
HELP-SYNTAX: \ $pretty-link{ $pretty-link ;
HELP-SYNTAX: \ $prettyprinting-note{ $prettyprinting-note ;
HELP-SYNTAX: \ $quotation{ $quotation ;
HELP-SYNTAX: \ $references{ $references ;
HELP-SYNTAX: \ $related{ $related ;
HELP-SYNTAX: \ $see{ $see ;
HELP-SYNTAX: \ $see-also{ $see-also ;
HELP-SYNTAX: \ $sequence{ $sequence ;
HELP-SYNTAX: \ $shuffle{ $shuffle ;
HELP-SYNTAX: \ $side-effects{ $side-effects ;
HELP-SYNTAX: \ $slot{ $slot ;
HELP-SYNTAX: \ $snippet{ $snippet ;
HELP-SYNTAX: \ $strong{ $strong ;
HELP-SYNTAX: \ $subheading{ $subheading ;
HELP-SYNTAX: \ $subsection{ $subsection ;
HELP-SYNTAX: \ $subsection*{ $subsection* ;
HELP-SYNTAX: \ $subsections{ $subsections ;
HELP-SYNTAX: \ $synopsis{ $synopsis ;
HELP-SYNTAX: \ $syntax{ $syntax ;
HELP-SYNTAX: \ $table{ $table ;
HELP-SYNTAX: \ $unchecked-example{ $unchecked-example ;
HELP-SYNTAX: \ $url{ $url ;
HELP-SYNTAX: \ $value{ $value ;
HELP-SYNTAX: \ $values{ $values ;
HELP-SYNTAX: \ $values-x/y{ $values-x/y ;
HELP-SYNTAX: \ $var-description{ $var-description ;
HELP-SYNTAX: \ $vocab-link{ $vocab-link ;
HELP-SYNTAX: \ $vocab-links{ $vocab-links ;
HELP-SYNTAX: \ $vocab-subsection{ $vocab-subsection ;
HELP-SYNTAX: \ $vocabulary{ $vocabulary ;
HELP-SYNTAX: \ $warning{ $warning ;
