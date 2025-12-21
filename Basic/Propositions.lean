import Basic.Ontology

/--
  Intensional negation on propositions.
-/
axiom neg : Propn → Propn

notation "¬ₚ" p => neg p
