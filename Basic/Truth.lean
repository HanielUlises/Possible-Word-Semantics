import PossibleWorldsSemantics.Basic.Ontology
import PossibleWorldsSemantics.Basic.Propositions

/-
  Truth at a world
-/

/--
  Truth of a proposition at a world.
-/
abbrev TrueIn (s : World) (p : PropW) : Prop :=
  p s

notation:50 s " ⊨ " p => TrueIn s p
