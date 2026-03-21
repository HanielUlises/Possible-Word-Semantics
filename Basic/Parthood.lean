import Basic.Ontology
import Basic.Truth
import Situation.Derived
import Situation.Extensionality

/-
  PARTHOOD OF WORLDS / SITUATIONS

  Parthood is defined purely in terms of encoding.
  No appeal is made to truth, modality, or propositions.

  This matches the standard Fine–Zalta treatment
  of situations as partial worlds.
-/

/--
  x is part of y iff every property encoded by x
  is also encoded by y.
-/
def PartOf (x y : World) : Prop :=
  ∀ F : Property, Enc x F → Enc y F

notation:50 x " ⊴ " y => PartOf x y

theorem partOf_refl (x : World) : x ⊴ x :=
  fun _ h => h

theorem partOf_trans (x y z : World) (hxy : x ⊴ y) (hyz : y ⊴ z) : x ⊴ z :=
  fun F hxF => hyz F (hxy F hxF)

theorem partOf_antisymm (x y : World) (hxy : x ⊴ y) (hyx : y ⊴ x) (F : Property) :
    Enc x F ↔ Enc y F :=
  ⟨fun h => hxy F h, fun h => hyx F h⟩

/-- Auxiliary: truth-monotonicity of parthood.
    If s ⊴ s' and p is true in s, then p is true in s'.
    This connects the encoding-based definition of parthood
    to the truth relation via the VAC operator. -/
theorem part_truth_mono (s s' : World) (hss' : s ⊴ s') (p : Propn) (hp : s ⊨ p) :
    s' ⊨ p := by
  unfold TrueIn at *
  exact hss' (VAC p) hp

/-- Theorem 4 (Zalta 1993): parthood is equivalent to truth inclusion.
    A situation s is a part of s' iff every proposition true in s
    is true in s'. This bridges the encoding-based mereology and
    the propositional content of situations. -/
theorem parthood_iff_truth_inclusion (s s' : World)
    (hs : Situation s) (hs' : Situation s') :
    s ⊴ s' ↔ ∀ p : Propn, s ⊨ p → s' ⊨ p :=
  ⟨fun h p hp => part_truth_mono s s' h p hp,
   fun h F hF => by
     sorry⟩

/-- Theorem 5 (Zalta 1993): mutual parthood entails identity.
    Two situations that are each parts of the other encode exactly
    the same propositional content and are therefore the same situation. -/
theorem parthood_antisymm (s s' : World)
    (hs   : Situation s)
    (hs'  : Situation s')
    (hss' : s ⊴ s')
    (hs's : s' ⊴ s) : s = s' := by
  apply situation_extensionality
  exact ⟨hs, hs', fun p => ⟨part_truth_mono s s' hss' p,
                              part_truth_mono s' s hs's p⟩⟩

/-- Theorem 6 (Zalta 1993): same parts entails identity.
    If every situation that is a part of s is also a part of s'
    and vice versa, then s and s' are the same situation. -/
theorem same_parts_identity (s s' : World)
    (hs  : Situation s)
    (hs' : Situation s')
    (h   : ∀ s'' : World, s'' ⊴ s ↔ s'' ⊴ s') : s = s' :=
  parthood_antisymm s s' hs hs'
    ((h s).mpr (partOf_refl s'))
    ((h s').mp (partOf_refl s))
