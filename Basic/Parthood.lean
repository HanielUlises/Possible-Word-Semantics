import Basic.Ontology

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

theorem partOf_refl (x : World) : x ⊴ x := by
  intro F h
  exact h

theorem partOf_trans (x y z : World) (hxy : x ⊴ y) (hyz : y ⊴ z) : x ⊴ z := by
  intro F hxF
  exact hyz F (hxy F hxF)

theorem partOf_antisymm (x y : World) (hxy : x ⊴ y) (hyx : y ⊴ x) (F : Property) :
    Enc x F ↔ Enc y F := by
  constructor
  · intro h; exact hxy F h
  · intro h; exact hyx F h
