import Basic.Truth

/-
  MODAL OPERATORS

  Modal notions are introduced axiomatically.
  We do not assume a Kripke frame or accessibility relation.
-/

/--
  Modal possibility operator.
-/
axiom Possibly : Prop → Prop

notation "◊" p => Possibly p

/-
  DERIVED MODAL CONCEPTS
-/

/--
  Persistence of a proposition.

  A proposition is persistent iff whenever it is true
  in a situation, it remains true in all larger situations.
-/
def Persistent (p : Propn) : Prop :=
  ∀ s s' : World, s ⊨ p → s ⊴ s' → s' ⊨ p

/--
  Actuality of a situation.

  A situation is actual iff every proposition true in it
  is true simpliciter.
-/

def Actual (s : World) : Prop :=
  ∀ p : Propn, s ⊨ p → True p

/--
  Possibility of a situation.
-/
def Possible (s : World) : Prop :=
  ◊ Actual s

/--
  Consistency of a situation.

  No proposition and its negation are both true in it.
-/
def Consistent (s : World) : Prop :=
  ¬ ∃ p : Propn, s ⊨ p ∧ s ⊨ ¬ₚ p
