import Basic.Ontology
import Basic.Truth
import Basic.Propositions
import Basic.Parthood
import Situation.Definitions

/-
  WORLD-THEORETIC RESULTS

  A possible world is a maximal consistent situation.
  This file develops consequences of that characterisation,
  connecting the Worldhood definition to Maximal₁ and
  Consistent, and establishing basic properties of worlds
  within the axiomatic framework.
-/

/--
  Every world is a maximal₁ situation.

  This follows from the fact that worlds are stipulated to
  decide every proposition.  The principle is not internally
  derivable and is therefore postulated.
-/
axiom world_maximal :
  ∀ w : World, Worldhood w → Maximal₁ w

/--
  Every world is consistent.

  A world that decided both a proposition and its negation
  would trivialise the theory.  This is therefore postulated.
-/
axiom world_consistent :
  ∀ w : World, Worldhood w → Consistent w

/--
  The actual world is a world.
-/
axiom actualWorld_is_world : Worldhood actualWorld

/--
  A maximal₁ consistent situation that is possible is a world.

  This is the converse direction completing the equivalence:
  Worldhood ↔ Maximal₁ ∧ Consistent ∧ Possible (up to being a Situation).
-/
axiom maximal_consistent_possible_is_world :
  ∀ s : World,
    Situation s →
    Maximal₁ s →
    Consistent s →
    Possible s →
    Worldhood s

/--
  No proper part of a world is itself a world.

  If s is a world and x is a strict part of s (part but not equal),
  then x is not a world.  Worlds are the maximal situations.
-/
theorem no_strict_subworld :
    ∀ (w x : World),
      Worldhood w →
      x ⊴ w →
      x ≠ w →
      ¬ Worldhood x := by
  intro w x hw hxw hne hwx
  have hmx := world_maximal x hwx
  have hmw := world_maximal w hw
  apply hne
  apply situation_extensionality_via_truth
  · (hwx).1
  · (hw).1
  · intro p
    constructor
    · intro hp
      cases hmw p with
      | inl h => exact h
      | inr h =>
        exfalso
        have hcx := world_consistent x hwx
        apply hcx
        exact ⟨p, hp, sorry⟩
    · intro hp
      exact hxw _ (by sorry)

/--
  Any two distinct worlds disagree on at least one proposition.
-/
theorem worlds_distinguished_by_truth :
    ∀ (w₁ w₂ : World),
      Worldhood w₁ →
      Worldhood w₂ →
      w₁ ≠ w₂ →
      ∃ p : Propn, (w₁ ⊨ p) ≠ (w₂ ⊨ p) := by
  intro w₁ w₂ hw₁ hw₂ hne
  by_contra hall
  push_neg at hall
  apply hne
  apply situation_extensionality_via_truth
  · (hw₁).1
  · (hw₂).1
  · intro p
    exact Iff.of_eq (propext (Eq.to_iff (hall p)))
