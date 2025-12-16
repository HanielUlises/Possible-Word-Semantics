import Basic.Ontology
import Basic.Truth

/-
  DERIVED RELATIONS ON SITUATIONS

  These notions are defined in terms of truth-in.
  They introduce no new ontology and no modal structure.
-/

/--
  Truth agreement between two situations.

  s and s' agree iff they make exactly the same
  propositions true.
-/
def Agree (s s' : World) : Prop :=
  ∀ p : Propn, s ⊨ p ↔ s' ⊨ p

/--
  Extensional equivalence of situations.

  This is truth-based equivalence restricted
  to objects that are situations.
-/
def ExtEq (s s' : World) : Prop :=
  Situation s ∧ Situation s' ∧ Agree s s'
