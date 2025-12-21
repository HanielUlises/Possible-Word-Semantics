import Modality.Frames
import Modality.Operators

/-
  MODAL SYSTEM S5

  S5 corresponds to universal accessibility:
  every world accesses every other world.

  Modally, this collapses iterated necessity
  and possibility.
-/

/--
  S5 frame condition.
-/
def S5_Frame : Prop :=
  (∀ w : World, R w w) ∧
  (∀ w u v : World, R w u → R u v → R w v) ∧
  (∀ w u : World, R w u → R u w)

/--
  Modal collapse in S5.

  ◊□p → □p
-/
axiom s5_collapse :
  ∀ (p : World → Prop) (w : World),
    ◊ (□ p) w → □ p w
