USING: accessors assocs chr.factor chr.factor.util chr.parser classes.tuple
kernel sequences strings terms ;

IN: chr.factor.intra-effect.maps


! * Reasoning for structural data values

! This kind of duplicates the info that is provided with Slot or Nth
! Predicates etc.  It is important not to create definitional circles here.
! Right now this is only used to accumulated literal values in a central place
! to have a way to check for literalizing objects.  This especially means that we don't
! do destructuring comparisons on this, like conflict checking.  Once a key is inserted,
! its value is supposed to be sound, or another pred needs to resolve the conflict.
! The specialization of information on this should thus be monotonic.  In particular,
! If we have a literal expression inserted into it, this cannot be refined further.

CHRAT: chr-intra-effect-maps {  }

PREFIX-RULES: { P{ CompMode } }

! Not checking for actual values, only key subsets!
CHR: subsume-map @ { Map ?o ?m } // { Map ?o ?n } --
[ ?n ?m key-subset? ] | ;

! No consistency check here!
CHR: combine-map @ // { Map ?o ?m } { Map ?o ?n } --
[ ?n ?m assoc-union :>> ?k ] | { Map ?o ?k } ;

CHR: forget-literal-object-slots @ { Eq ?o A{ ?v } } // { Slot ?o __ __ } -- | ;

! CHR: literal-implies-local-alloc @ { Eq ?o A{ ?v } } // { LocalAllocation ?o } -- | ;

! This is kind of the slots value-info structure attached to compiler values
! FIXME: unifier seems to go haywire on Hashtables...
! CHR: slot-defines-map @ { Slot ?o ?n ?v } // -- | { Map ?o H{ { ?n ?v } } } ;
! NOTE: only do this for named slots right now
CHR: slot-literal-defines-map @ { Slot ?o Is( string ?n ) M{ ?v } } { Eq M{ ?v } A{ ?a } } // -- | { Map ?o { { ?n ?a } } } ;

: assoc>tuple ( assoc class -- obj )
    [ all-slots [ name>> of ] with map ] [ slots>tuple ] bi ;

CHR: literalize-tuple @ { Instance ?o Is( tuple-class ?tau ) } // { Map M{ ?o } A{ ?m } } --
[ ?tau all-slots :>> ?s ]
[ ?s [ [ read-only>> ]
       [ name>> ?m key? ]
       ! [ name>> ?m at ground-value? ]
       bi and ] all? ]
[ ?m ?tau assoc>tuple :>> ?v ]
| { Eq ?o ?v } ;


;
