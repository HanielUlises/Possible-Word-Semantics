import Modality.Frames
import Modality.Operators

/-
  MODAL SYSTEM S4

  S4 is characterized semantically by reflexive
  and transitive accessibility.

  What is necessary is true
  necessity is stable under iteration
-/

/--
  S4 frame condition.
-/
def S4_Frame : Prop :=
  (∀ w : World, R w w) ∧
  (∀ w u v : World, R w u → R u v → R w v)

/--
  Necessitation is idempotent in S4.

  □p → □□p
-/
axiom box_idempotent :
  ∀ (p : World → Prop) (w : World),
    □ p w → □ (□ p) w
