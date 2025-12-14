import Basic.Ontology
import Basic.Propositions

universe u
universe v

/-
  TRUTH IN SITUATIONS

  Truth is relativized to situations.
  Truth-in is taken as primitive.
-/

/--
  Truth of a proposition in a world or situation.
-/
axiom TrueIn : World → Propn → Prop

notation:50 s " ⊨ " p => TrueIn s p

/-
  PART–WHOLE RELATION

  x is part of y iff every property encoded by x
  is also encoded by y.
-/

/--
  Parthood relation on worlds/situations.

  Formally:
    x ⊴ y  ≝  ∀F (x encodes F → y encodes F)
-/
def PartOf (x y : World) : Prop :=
  ∀ (F : Property.{v}), Enc x F → Enc y F

notation:50 x " ⊴ " y => PartOf x y
