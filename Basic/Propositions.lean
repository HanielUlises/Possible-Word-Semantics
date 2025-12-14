/-
  PROPOSITIONS

  Propositions are treated as primitive intensional entities,
  not as syntactic formulas or truth values.

  This aligns with possible-worlds semantics where propositions
  are evaluated relative to situations.
-/

/--
  The type of propositions.
-/
axiom Propn : Type

/--
  Negation on propositions.

  This is propositional negation at the intensional level,
  not Boolean negation in the metalanguage.
-/
axiom neg : Propn → Propn

notation "¬ₚ" p => neg p
