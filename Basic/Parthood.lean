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
