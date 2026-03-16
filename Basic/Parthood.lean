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

theorem partOf_refl : ∀ x : World, x ⊴ x :=
  fun _ _ h => h

theorem partOf_trans :
    ∀ x y z : World, x ⊴ y → y ⊴ z → x ⊴ z :=
  fun _ _ _ hxy hyz F hxF => hyz F (hxy F hxF)

theorem partOf_antisymm :
    ∀ x y : World,
      x ⊴ y → y ⊴ x →
      (∀ F : Property, Enc x F ↔ Enc y F) :=
  fun _ _ hxy hyx F =>
    ⟨fun h => hxy F h, fun h => hyx F h⟩
