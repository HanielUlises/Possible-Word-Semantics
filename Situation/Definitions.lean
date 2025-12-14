import Basic.Truth
import Modality.Operators

/-- Actuality: everything true in s is true simpliciter -/
def Actual (s : World) : Prop :=
  ∀ p : Propn, s ⊨ p → True

/-- Possible situation -/
def Possible (s : World) : Prop :=
  ◊ (Actual s)

/-- Worldhood (full biconditional version) -/
def Worldhood (s : World) : Prop :=
  Situation s ∧ ◊ (∀ p : Propn, s ⊨ p ↔ True)

/-- Maximality (sense 1) -/
def Maximal₁ (s : World) : Prop :=
  ∀ p : Propn, s ⊨ p ∨ s ⊨ ¬ₚ p

/-- Partiality (sense 1) -/
def Partial₁ (s : World) : Prop :=
  ∃ p : Propn, ¬ (s ⊨ p) ∧ ¬ (s ⊨ ¬ₚ p)

/-- Maximality (sense 2) -/
def Maximal₂ (s : World) : Prop :=
  ∀ p : Propn, s ⊨ p

/-- Partiality (sense 2) -/
def Partial₂ (s : World) : Prop :=
  ∃ p : Propn, ¬ (s ⊨ p)

/-- Consistency -/
def Consistent (s : World) : Prop :=
  ¬ ∃ p : Propn, s ⊨ p ∧ s ⊨ ¬ₚ p
