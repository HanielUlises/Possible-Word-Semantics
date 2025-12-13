universe u

/-
  Primitive ontology
-/

/-- Worlds / situations are primitive entities -/
axiom World : Type u

/-- Situations (a distinguished class of worlds) -/
axiom Situation : World → Prop
