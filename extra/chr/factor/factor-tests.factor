USING: chr.factor chr.factor.conditions chr.factor.quotations chr.parser
chr.state lists terms tools.test ;
IN: chr.factor.tests


TERM-VARS: s1 st1 sf1 rho a v sig x y s ;
: wake-problem ( -- x )
    {
        P{ Branch s st1 sf1 }
        P{ Cond st1 P{ SameStack rho a } }
        P{ Cond st1 P{ SameStack L{ v . a } sig } }
        P{ Cond sf1 P{ SameStack rho L{ y x . rho } } }
        P{ Cond sf1 P{ SameStack L{ x y . rho } sig } }
    } ;

[ \ expand-quot wake-problem query-with ] [ imbalanced-branch-stacks? ] must-fail-with
