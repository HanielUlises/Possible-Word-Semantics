import Grounding.Ontology
import Grounding.Truth
import Situation.Derived
import Situation.Extensionality

def PartOf (x y : World) : Prop :=
  ∀ F : Property, Enc x F → Enc y F

notation:15 x " ⊴ " y => PartOf x y

theorem partOf_refl (x : World) : x ⊴ x :=
  fun _ h => h

theorem partOf_trans (x y z : World) (hxy : x ⊴ y) (hyz : y ⊴ z) : x ⊴ z :=
  fun F hxF => hyz F (hxy F hxF)

theorem partOf_antisymm_enc (x y : World) (hxy : x ⊴ y) (hyx : y ⊴ x) (F : Property) :
    Enc x F ↔ Enc y F :=
  ⟨fun h => hxy F h, fun h => hyx F h⟩

/-
  Open proof obligation OP-2: Parthood via truth-monotonicity.
  Open proof obligation OP-3: Situations are objects.
  See README.md § Open Proof Obligations.
-/

/-- Auxiliary: parthood implies truth-monotonicity.
    Blocked by OP-3. -/
theorem part_truth_mono (s s' : World)
    (hs   : Situation s)
    (hs'  : Situation s')
    (hss' : s ⊴ s')
    (p    : Propn)
    (hp   : s ⊨ p) : s' ⊨ p := by
  sorry -- OP-3

/-- Theorem 4 (Zalta 1993): parthood is equivalent to truth inclusion.
    Blocked by OP-2 and OP-3. -/
theorem parthood_iff_truth_inclusion (s s' : World)
    (hs  : Situation s)
    (hs' : Situation s') :
    (s ⊴ s') ↔ (∀ p : Propn, (s ⊨ p) → (s' ⊨ p)) := by
  constructor
  · intro h p hp
    exact part_truth_mono s s' hs hs' h p hp
  · intro h
    sorry -- OP-2

/-- Theorem 5 (Zalta 1993): mutual parthood entails identity.
    Blocked by OP-2 and OP-3. -/
theorem parthood_antisymm (s s' : World)
    (hs   : Situation s)
    (hs'  : Situation s')
    (hss' : s ⊴ s')
    (hs's : s' ⊴ s) : s = s' := by
  apply situation_extensionality
  exact ⟨hs, hs', fun p =>
    ⟨part_truth_mono s s' hs hs' hss' p,
     part_truth_mono s' s hs' hs hs's p⟩⟩

/-- Theorem 6 (Zalta 1993): same parts entails identity.
    Follows from Theorem 5 once OP-2 and OP-3 are resolved. -/
theorem same_parts_identity (s s' : World)
    (hs  : Situation s)
    (hs' : Situation s')
    (h   : ∀ s'' : World, (s'' ⊴ s) ↔ (s'' ⊴ s')) : s = s' := by
  apply parthood_antisymm s s' hs hs'
  · exact (h s).mp (partOf_refl s)
  · exact (h s').mpr (partOf_refl s')
