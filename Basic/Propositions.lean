import Basic.Ontology

/--
  Intensional negation on propositions.
-/
axiom neg : Propn → Propn

notation "¬ₚ" p => neg p

/--
  Intensional conjunction of propositions.
-/
axiom conj : Propn → Propn → Propn

infixl:70 " ∧ₚ " => conj

/--
  Intensional disjunction of propositions.
-/
axiom disj : Propn → Propn → Propn

infixl:65 " ∨ₚ " => disj

/--
  Intensional implication between propositions.
-/
axiom impl : Propn → Propn → Propn

infixr:60 " →ₚ " => impl

/--
  Double negation: ¬ₚ¬ₚp is intensionally identical to p.

  This corresponds to the Boolean principle that two
  negations cancel at the level of propositional identity.
-/
axiom neg_neg : ∀ p : Propn, neg (neg p) = p

/--
  De Morgan for conjunction: ¬ₚ(p ∧ₚ q) = ¬ₚp ∨ₚ ¬ₚq.
-/
axiom deMorgan_conj :
  ∀ p q : Propn, neg (conj p q) = disj (neg p) (neg q)

/--
  De Morgan for disjunction: ¬ₚ(p ∨ₚ q) = ¬ₚp ∧ₚ ¬ₚq.
-/
axiom deMorgan_disj :
  ∀ p q : Propn, neg (disj p q) = conj (neg p) (neg q)
