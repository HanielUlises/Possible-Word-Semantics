import Grounding.Ontology
import Grounding.Truth
import Situation.Derived
import Situation.Extensionality

/-
  PARTHOOD OF WORLDS / SITUATIONS

  Parthood is defined purely in terms of encoding.
  No appeal is made to truth, modality, or propositions
  at the definitional level.

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

theorem partOf_antisymm_enc (x y : World) (hxy : x ⊴ y) (hyx : y ⊴ x) (F : Property) :
    Enc x F ↔ Enc y F :=
  ⟨fun h => hxy F h, fun h => hyx F h⟩

/-
  Open proof obligation OP-2: Parthood via truth-monotonicity.

  PartOf is defined over Enc. TrueIn is a separate primitive.
  The direction (∀ p, s ⊨ p → s' ⊨ p) → s ⊴ s' is not derivable
  from the current axiom inventory.

  See README.md § Open Proof Obligations, OP-2.
  Candidate resolution:
    axiom truth_mono_to_part :
      ∀ s s' : World, (∀ p : Propn, s ⊨ p → s' ⊨ p) → s ⊴ s'

  Open proof obligation OP-3: Situations are objects.

  TrueIn_def and Encp_def both require Object x as a hypothesis.
  Situation and Object are independent predicates. There is no axiom
  asserting Situation s → Object s.

  See README.md Open Proof Obligations, OP-3.
  Candidate resolution:
    axiom situation_is_object : ∀ s : World, Situation s → Object s
-/

/-- Auxiliary: parthood implies truth-monotonicity.
    If s ⊴ s' then every proposition true in s is true in s'.

    OP-3: requires situation_is_object to discharge the Object
    hypothesis of TrueIn_def and Encp_def. Marked sorry until
    OP-3 is resolved. -/
theorem part_truth_mono (s s' : World)
    (hs   : Situation s)
    (hs'  : Situation s')
    (hss' : s ⊴ s')
    (p    : Propn)
    (hp   : s ⊨ p) : s' ⊨ p := by
  -- OP-3: need situation_is_object to get Object s and Object s'
  -- then unfold via TrueIn_def and Encp_def on both sides
  sorry -- OP-3

/-- Theorem 4 (Zalta 1993): parthood is equivalent to truth inclusion.
    A situation s is a part of s' iff every proposition true in s
    is true in s'.

    The (->) direction follows from part_truth_mono.
    The (<-) direction requires truth_mono_to_part (OP-2).
    Both directions require situation_is_object (OP-3).

    Blocked by OP-2 and OP-3. See README.md § Open Proof Obligations. -/
theorem parthood_iff_truth_inclusion (s s' : World)
    (hs  : Situation s)
    (hs' : Situation s') :
    s ⊴ s' ↔ ∀ p : Propn, s ⊨ p → s' ⊨ p := by
  constructor
  · intro h p hp
    exact part_truth_mono s s' hs hs' h p hp
  · intro h
    sorry -- OP-2: requires truth_mono_to_part

/-- Theorem 5 (Zalta 1993): mutual parthood entails identity.
    Two situations that are each parts of the other encode exactly
    the same propositional content and are therefore the same situation.

    Blocked by OP-2 and OP-3 via parthood_iff_truth_inclusion.
    See README.md § Open Proof Obligations. -/
theorem parthood_antisymm (s s' : World)
    (hs   : Situation s)
    (hs'  : Situation s')
    (hss' : s ⊴ s')
    (hs's : s' ⊴ s) : s = s' :=
  situation_extensionality ⟨hs, hs', fun p =>
    ⟨part_truth_mono s s' hs hs' hss' p, -- blocked by OP3
     part_truth_mono s' s hs' hs hs's p⟩⟩ -- blocked by OP3

/-- Theorem 6 (Zalta 1993): same parts entails identity.
    If every situation that is a part of s is also a part of s'
    and vice versa, then s and s' are the same situation.

    Follows from Theorem 5 once OP-2 and OP-3 are resolved. -/
theorem same_parts_identity (s s' : World)
    (hs  : Situation s)
    (hs' : Situation s')
    (h   : ∀ s'' : World, s'' ⊴ s ↔ s'' ⊴ s') : s = s' :=
  parthood_antisymm s s' hs hs'
    ((h s).mpr  (partOf_refl s'))
    ((h s').mp  (partOf_refl s))
