import Basic.Ontology
import Situation.Derived

/--
  Extensionality of situations.

  This principle is postulated rather than derived.
  It reflects the constitutive assumption that situations
  are fully determined by their propositional content.
-/
axiom situation_extensionality :
  ∀ s s' : World, ExtEq s s' → s = s'
