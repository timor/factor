! Copyright (C) 2005, 2009 Slava Pestov.
! See http://factorcode.org/license.txt for BSD license.
USING: accessors arrays compiler.units definitions help
help.markup help.topics kernel lexer math multiline namespaces
parser quotations sequences splitting vocabs.parser words ;
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
SYNTAX: \ HELP-ARRAY:
    scan-new-escaped scan-word ";" expect
    $[ \ } parse-until split-dashes >array _ prefix suffix! ] define-syntax ;

SYNTAX: \ HELP-STRING:
    scan-new-escaped scan-word ";" expect
    $[ _ "\"" parse-multiline-string-new 2array suffix! ] define-syntax ;

SYNTAX: \ HELP-BACKTICK:
    scan-new-escaped scan-word ";" expect
    $[ _ lexer get parse-spaceless-payload 2array suffix! ] define-syntax ;

SYNTAX: \ HELP-2BACKTICKS:
    scan-new-escaped scan-word ";" expect
    $[ _ "``" parse-multiline-string-new 2array suffix! ] define-syntax ;

SYNTAX: \ HELP-3BACKTICKS:
    scan-new-escaped scan-word ";" expect
    $[ _ "```" parse-multiline-string-new 2array suffix! ] define-syntax ;

COMPILE>

HELP-ARRAY: \ $breadcrumbs{ $breadcrumbs ;
HELP-ARRAY: \ $class-description{ $class-description ;
HELP-ARRAY: \ $code{ $code ;
HELP-ARRAY: \ $complex-shuffle{ $complex-shuffle ;
HELP-ARRAY: \ $content{ $content ;
HELP-ARRAY: \ $contract{ $contract ;
HELP-ARRAY: \ $curious{ $curious ;
HELP-ARRAY: \ $definition{ $definition ;
HELP-ARRAY: \ $definition-icons{ $definition-icons ;
HELP-ARRAY: \ $deprecated{ $deprecated ;
HELP-ARRAY: \ $description{ $description ;
HELP-ARRAY: \ $emphasis{ $emphasis ;
HELP-ARRAY: \ $error-description{ $error-description ;
HELP-ARRAY: \ $errors{ $errors ;
HELP-ARRAY: \ $example{ $example ;
HELP-ARRAY: \ $examples{ $examples ;
HELP-ARRAY: \ $heading{ $heading ;
HELP-ARRAY: \ $image{ $image ;
HELP-ARRAY: \ $instance{ $instance ;
HELP-ARRAY: \ $io-error{ $io-error ;
HELP-ARRAY: \ $link{ $link ;
HELP-ARRAY: \ $links{ $links ;
HELP-ARRAY: \ $list{ $list ;
HELP-ARRAY: \ $long-link{ $long-link ;
HELP-ARRAY: \ $low-level-note{ $low-level-note ;
HELP-ARRAY: \ $markup-example{ $markup-example ;
HELP-ARRAY: \ $maybe{ $maybe ;
HELP-ARRAY: \ $methods{ $methods ;
HELP-ARRAY: \ $nl{ $nl ;
HELP-ARRAY: \ $notes{ $notes ;
HELP-ARRAY: \ $or{ $or ;
HELP-ARRAY: \ $parsing-note{ $parsing-note ;
HELP-ARRAY: \ $pretty-link{ $pretty-link ;
HELP-ARRAY: \ $prettyprinting-note{ $prettyprinting-note ;
HELP-ARRAY: \ $quotation{ $quotation ;
HELP-ARRAY: \ $references{ $references ;
HELP-ARRAY: \ $related{ $related ;
HELP-ARRAY: \ $see{ $see ;
HELP-ARRAY: \ $see-also{ $see-also ;
HELP-ARRAY: \ $sequence{ $sequence ;
HELP-ARRAY: \ $shuffle{ $shuffle ;
HELP-ARRAY: \ $side-effects{ $side-effects ;
HELP-ARRAY: \ $slot{ $slot ;
HELP-ARRAY: \ $snippet{ $snippet ;
HELP-ARRAY: \ $strong{ $strong ;
HELP-ARRAY: \ $subheading{ $subheading ;
HELP-ARRAY: \ $subsection{ $subsection ;
HELP-ARRAY: \ $subsection*{ $subsection* ;
HELP-ARRAY: \ $subsections{ $subsections ;
HELP-ARRAY: \ $synopsis{ $synopsis ;
HELP-ARRAY: \ $syntax{ $syntax ;
HELP-ARRAY: \ $table{ $table ;
HELP-ARRAY: \ $unchecked-example{ $unchecked-example ;
HELP-ARRAY: \ $url{ $url ;
HELP-ARRAY: \ $value{ $value ;
HELP-ARRAY: \ $values{ $values ;
HELP-ARRAY: \ $values-x/y{ $values-x/y ;
HELP-ARRAY: \ $var-description{ $var-description ;
HELP-ARRAY: \ $vocab-link{ $vocab-link ;
HELP-ARRAY: \ $vocab-links{ $vocab-links ;
HELP-ARRAY: \ $vocab-subsection{ $vocab-subsection ;
HELP-ARRAY: \ $vocabulary{ $vocabulary ;
HELP-ARRAY: \ $warning{ $warning ;

HELP-STRING: \ $breadcrumbs" $breadcrumbs ;
HELP-STRING: \ $class-description" $class-description ;
HELP-STRING: \ $code" $code ;
HELP-STRING: \ $complex-shuffle" $complex-shuffle ;
HELP-STRING: \ $content" $content ;
HELP-STRING: \ $contract" $contract ;
HELP-STRING: \ $curious" $curious ;
HELP-STRING: \ $definition" $definition ;
HELP-STRING: \ $definition-icons" $definition-icons ;
HELP-STRING: \ $deprecated" $deprecated ;
HELP-STRING: \ $description" $description ;
HELP-STRING: \ $emphasis" $emphasis ;
HELP-STRING: \ $error-description" $error-description ;
HELP-STRING: \ $errors" $errors ;
HELP-STRING: \ $example" $example ;
HELP-STRING: \ $examples" $examples ;
HELP-STRING: \ $heading" $heading ;
HELP-STRING: \ $image" $image ;
HELP-STRING: \ $instance" $instance ;
HELP-STRING: \ $io-error" $io-error ;
HELP-STRING: \ $link" $link ;
HELP-STRING: \ $links" $links ;
HELP-STRING: \ $list" $list ;
HELP-STRING: \ $long-link" $long-link ;
HELP-STRING: \ $low-level-note" $low-level-note ;
HELP-STRING: \ $markup-example" $markup-example ;
HELP-STRING: \ $maybe" $maybe ;
HELP-STRING: \ $methods" $methods ;
HELP-STRING: \ $nl" $nl ;
HELP-STRING: \ $notes" $notes ;
HELP-STRING: \ $or" $or ;
HELP-STRING: \ $parsing-note" $parsing-note ;
HELP-STRING: \ $pretty-link" $pretty-link ;
HELP-STRING: \ $prettyprinting-note" $prettyprinting-note ;
HELP-STRING: \ $quotation" $quotation ;
HELP-STRING: \ $references" $references ;
HELP-STRING: \ $related" $related ;
HELP-STRING: \ $see" $see ;
HELP-STRING: \ $see-also" $see-also ;
HELP-STRING: \ $sequence" $sequence ;
HELP-STRING: \ $shuffle" $shuffle ;
HELP-STRING: \ $side-effects" $side-effects ;
HELP-STRING: \ $slot" $slot ;
HELP-STRING: \ $snippet" $snippet ;
HELP-STRING: \ $strong" $strong ;
HELP-STRING: \ $subheading" $subheading ;
HELP-STRING: \ $subsection" $subsection ;
HELP-STRING: \ $subsection*" $subsection* ;
HELP-STRING: \ $subsections" $subsections ;
HELP-STRING: \ $synopsis" $synopsis ;
HELP-STRING: \ $syntax" $syntax ;
HELP-STRING: \ $table" $table ;
HELP-STRING: \ $unchecked-example" $unchecked-example ;
HELP-STRING: \ $url" $url ;
HELP-STRING: \ $value" $value ;
HELP-STRING: \ $values" $values ;
HELP-STRING: \ $values-x/y" $values-x/y ;
HELP-STRING: \ $var-description" $var-description ;
HELP-STRING: \ $vocab-link" $vocab-link ;
HELP-STRING: \ $vocab-links" $vocab-links ;
HELP-STRING: \ $vocab-subsection" $vocab-subsection ;
HELP-STRING: \ $vocabulary" $vocabulary ;
HELP-STRING: \ $warning" $warning ;

HELP-BACKTICK: \ $breadcrumbs` $breadcrumbs ;
HELP-BACKTICK: \ $class-description` $class-description ;
HELP-BACKTICK: \ $code` $code ;
HELP-BACKTICK: \ $complex-shuffle` $complex-shuffle ;
HELP-BACKTICK: \ $content` $content ;
HELP-BACKTICK: \ $contract` $contract ;
HELP-BACKTICK: \ $curious` $curious ;
HELP-BACKTICK: \ $definition` $definition ;
HELP-BACKTICK: \ $definition-icons` $definition-icons ;
HELP-BACKTICK: \ $deprecated` $deprecated ;
HELP-BACKTICK: \ $description` $description ;
HELP-BACKTICK: \ $emphasis` $emphasis ;
HELP-BACKTICK: \ $error-description` $error-description ;
HELP-BACKTICK: \ $errors` $errors ;
HELP-BACKTICK: \ $example` $example ;
HELP-BACKTICK: \ $examples` $examples ;
HELP-BACKTICK: \ $heading` $heading ;
HELP-BACKTICK: \ $image` $image ;
HELP-BACKTICK: \ $instance` $instance ;
HELP-BACKTICK: \ $io-error` $io-error ;
HELP-BACKTICK: \ $link` $link ;
HELP-BACKTICK: \ $links` $links ;
HELP-BACKTICK: \ $list` $list ;
HELP-BACKTICK: \ $long-link` $long-link ;
HELP-BACKTICK: \ $low-level-note` $low-level-note ;
HELP-BACKTICK: \ $markup-example` $markup-example ;
HELP-BACKTICK: \ $maybe` $maybe ;
HELP-BACKTICK: \ $methods` $methods ;
HELP-BACKTICK: \ $nl` $nl ;
HELP-BACKTICK: \ $notes` $notes ;
HELP-BACKTICK: \ $or` $or ;
HELP-BACKTICK: \ $parsing-note` $parsing-note ;
HELP-BACKTICK: \ $pretty-link` $pretty-link ;
HELP-BACKTICK: \ $prettyprinting-note` $prettyprinting-note ;
HELP-BACKTICK: \ $quotation` $quotation ;
HELP-BACKTICK: \ $references` $references ;
HELP-BACKTICK: \ $related` $related ;
HELP-BACKTICK: \ $see` $see ;
HELP-BACKTICK: \ $see-also` $see-also ;
HELP-BACKTICK: \ $sequence` $sequence ;
HELP-BACKTICK: \ $shuffle` $shuffle ;
HELP-BACKTICK: \ $side-effects` $side-effects ;
HELP-BACKTICK: \ $slot` $slot ;
HELP-BACKTICK: \ $snippet` $snippet ;
HELP-BACKTICK: \ $strong` $strong ;
HELP-BACKTICK: \ $subheading` $subheading ;
HELP-BACKTICK: \ $subsection` $subsection ;
HELP-BACKTICK: \ $subsection*` $subsection* ;
HELP-BACKTICK: \ $subsections` $subsections ;
HELP-BACKTICK: \ $synopsis` $synopsis ;
HELP-BACKTICK: \ $syntax` $syntax ;
HELP-BACKTICK: \ $table` $table ;
HELP-BACKTICK: \ $unchecked-example` $unchecked-example ;
HELP-BACKTICK: \ $url` $url ;
HELP-BACKTICK: \ $value` $value ;
HELP-BACKTICK: \ $values` $values ;
HELP-BACKTICK: \ $values-x/y` $values-x/y ;
HELP-BACKTICK: \ $var-description` $var-description ;
HELP-BACKTICK: \ $vocab-link` $vocab-link ;
HELP-BACKTICK: \ $vocab-links` $vocab-links ;
HELP-BACKTICK: \ $vocab-subsection` $vocab-subsection ;
HELP-BACKTICK: \ $vocabulary` $vocabulary ;
HELP-BACKTICK: \ $warning` $warning ;

HELP-2BACKTICKS: \ $breadcrumbs`` $breadcrumbs ;
HELP-2BACKTICKS: \ $class-description`` $class-description ;
HELP-2BACKTICKS: \ $code`` $code ;
HELP-2BACKTICKS: \ $complex-shuffle`` $complex-shuffle ;
HELP-2BACKTICKS: \ $content`` $content ;
HELP-2BACKTICKS: \ $contract`` $contract ;
HELP-2BACKTICKS: \ $curious`` $curious ;
HELP-2BACKTICKS: \ $definition`` $definition ;
HELP-2BACKTICKS: \ $definition-icons`` $definition-icons ;
HELP-2BACKTICKS: \ $deprecated`` $deprecated ;
HELP-2BACKTICKS: \ $description`` $description ;
HELP-2BACKTICKS: \ $emphasis`` $emphasis ;
HELP-2BACKTICKS: \ $error-description`` $error-description ;
HELP-2BACKTICKS: \ $errors`` $errors ;
HELP-2BACKTICKS: \ $example`` $example ;
HELP-2BACKTICKS: \ $examples`` $examples ;
HELP-2BACKTICKS: \ $heading`` $heading ;
HELP-2BACKTICKS: \ $image`` $image ;
HELP-2BACKTICKS: \ $instance`` $instance ;
HELP-2BACKTICKS: \ $io-error`` $io-error ;
HELP-2BACKTICKS: \ $link`` $link ;
HELP-2BACKTICKS: \ $links`` $links ;
HELP-2BACKTICKS: \ $list`` $list ;
HELP-2BACKTICKS: \ $long-link`` $long-link ;
HELP-2BACKTICKS: \ $low-level-note`` $low-level-note ;
HELP-2BACKTICKS: \ $markup-example`` $markup-example ;
HELP-2BACKTICKS: \ $maybe`` $maybe ;
HELP-2BACKTICKS: \ $methods`` $methods ;
HELP-2BACKTICKS: \ $nl`` $nl ;
HELP-2BACKTICKS: \ $notes`` $notes ;
HELP-2BACKTICKS: \ $or`` $or ;
HELP-2BACKTICKS: \ $parsing-note`` $parsing-note ;
HELP-2BACKTICKS: \ $pretty-link`` $pretty-link ;
HELP-2BACKTICKS: \ $prettyprinting-note`` $prettyprinting-note ;
HELP-2BACKTICKS: \ $quotation`` $quotation ;
HELP-2BACKTICKS: \ $references`` $references ;
HELP-2BACKTICKS: \ $related`` $related ;
HELP-2BACKTICKS: \ $see`` $see ;
HELP-2BACKTICKS: \ $see-also`` $see-also ;
HELP-2BACKTICKS: \ $sequence`` $sequence ;
HELP-2BACKTICKS: \ $shuffle`` $shuffle ;
HELP-2BACKTICKS: \ $side-effects`` $side-effects ;
HELP-2BACKTICKS: \ $slot`` $slot ;
HELP-2BACKTICKS: \ $snippet`` $snippet ;
HELP-2BACKTICKS: \ $strong`` $strong ;
HELP-2BACKTICKS: \ $subheading`` $subheading ;
HELP-2BACKTICKS: \ $subsection`` $subsection ;
HELP-2BACKTICKS: \ $subsection*`` $subsection* ;
HELP-2BACKTICKS: \ $subsections`` $subsections ;
HELP-2BACKTICKS: \ $synopsis`` $synopsis ;
HELP-2BACKTICKS: \ $syntax`` $syntax ;
HELP-2BACKTICKS: \ $table`` $table ;
HELP-2BACKTICKS: \ $unchecked-example`` $unchecked-example ;
HELP-2BACKTICKS: \ $url`` $url ;
HELP-2BACKTICKS: \ $value`` $value ;
HELP-2BACKTICKS: \ $values`` $values ;
HELP-2BACKTICKS: \ $values-x/y`` $values-x/y ;
HELP-2BACKTICKS: \ $var-description`` $var-description ;
HELP-2BACKTICKS: \ $vocab-link`` $vocab-link ;
HELP-2BACKTICKS: \ $vocab-links`` $vocab-links ;
HELP-2BACKTICKS: \ $vocab-subsection`` $vocab-subsection ;
HELP-2BACKTICKS: \ $vocabulary`` $vocabulary ;
HELP-2BACKTICKS: \ $warning`` $warning ;

HELP-3BACKTICKS: \ $breadcrumbs``` $breadcrumbs ;
HELP-3BACKTICKS: \ $class-description``` $class-description ;
HELP-3BACKTICKS: \ $code``` $code ;
HELP-3BACKTICKS: \ $complex-shuffle``` $complex-shuffle ;
HELP-3BACKTICKS: \ $content``` $content ;
HELP-3BACKTICKS: \ $contract``` $contract ;
HELP-3BACKTICKS: \ $curious``` $curious ;
HELP-3BACKTICKS: \ $definition``` $definition ;
HELP-3BACKTICKS: \ $definition-icons``` $definition-icons ;
HELP-3BACKTICKS: \ $deprecated``` $deprecated ;
HELP-3BACKTICKS: \ $description``` $description ;
HELP-3BACKTICKS: \ $emphasis``` $emphasis ;
HELP-3BACKTICKS: \ $error-description``` $error-description ;
HELP-3BACKTICKS: \ $errors``` $errors ;
HELP-3BACKTICKS: \ $example``` $example ;
HELP-3BACKTICKS: \ $examples``` $examples ;
HELP-3BACKTICKS: \ $heading``` $heading ;
HELP-3BACKTICKS: \ $image``` $image ;
HELP-3BACKTICKS: \ $instance``` $instance ;
HELP-3BACKTICKS: \ $io-error``` $io-error ;
HELP-3BACKTICKS: \ $link``` $link ;
HELP-3BACKTICKS: \ $links``` $links ;
HELP-3BACKTICKS: \ $list``` $list ;
HELP-3BACKTICKS: \ $long-link``` $long-link ;
HELP-3BACKTICKS: \ $low-level-note``` $low-level-note ;
HELP-3BACKTICKS: \ $markup-example``` $markup-example ;
HELP-3BACKTICKS: \ $maybe``` $maybe ;
HELP-3BACKTICKS: \ $methods``` $methods ;
HELP-3BACKTICKS: \ $nl``` $nl ;
HELP-3BACKTICKS: \ $notes``` $notes ;
HELP-3BACKTICKS: \ $or``` $or ;
HELP-3BACKTICKS: \ $parsing-note``` $parsing-note ;
HELP-3BACKTICKS: \ $pretty-link``` $pretty-link ;
HELP-3BACKTICKS: \ $prettyprinting-note``` $prettyprinting-note ;
HELP-3BACKTICKS: \ $quotation``` $quotation ;
HELP-3BACKTICKS: \ $references``` $references ;
HELP-3BACKTICKS: \ $related``` $related ;
HELP-3BACKTICKS: \ $see``` $see ;
HELP-3BACKTICKS: \ $see-also``` $see-also ;
HELP-3BACKTICKS: \ $sequence``` $sequence ;
HELP-3BACKTICKS: \ $shuffle``` $shuffle ;
HELP-3BACKTICKS: \ $side-effects``` $side-effects ;
HELP-3BACKTICKS: \ $slot``` $slot ;
HELP-3BACKTICKS: \ $snippet``` $snippet ;
HELP-3BACKTICKS: \ $strong``` $strong ;
HELP-3BACKTICKS: \ $subheading``` $subheading ;
HELP-3BACKTICKS: \ $subsection``` $subsection ;
HELP-3BACKTICKS: \ $subsection*``` $subsection* ;
HELP-3BACKTICKS: \ $subsections``` $subsections ;
HELP-3BACKTICKS: \ $synopsis``` $synopsis ;
HELP-3BACKTICKS: \ $syntax``` $syntax ;
HELP-3BACKTICKS: \ $table``` $table ;
HELP-3BACKTICKS: \ $unchecked-example``` $unchecked-example ;
HELP-3BACKTICKS: \ $url``` $url ;
HELP-3BACKTICKS: \ $value``` $value ;
HELP-3BACKTICKS: \ $values``` $values ;
HELP-3BACKTICKS: \ $values-x/y``` $values-x/y ;
HELP-3BACKTICKS: \ $var-description``` $var-description ;
HELP-3BACKTICKS: \ $vocab-link``` $vocab-link ;
HELP-3BACKTICKS: \ $vocab-links``` $vocab-links ;
HELP-3BACKTICKS: \ $vocab-subsection``` $vocab-subsection ;
HELP-3BACKTICKS: \ $vocabulary``` $vocabulary ;
HELP-3BACKTICKS: \ $warning``` $warning ;
