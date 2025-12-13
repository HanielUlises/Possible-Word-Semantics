import PossibleWorldsSemantics.Basic.Ontology

universe u

/-
  Propositions
-/

/--
  Propositions are predicates on worlds.
  This is a higher-order semantics.
-/
abbrev PropW := World → Prop
