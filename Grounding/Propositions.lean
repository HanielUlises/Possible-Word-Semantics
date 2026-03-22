import Basic.Ontology

/--
  Intensional negation on propositions.
-/
axiom neg : Propn → Propn

notation "¬ₚ" => neg

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
  Intensional biconditional between propositions.

  Defined as mutual implication at the propositional level.
  This is not definitional equality but intensional equivalence:
  p ⟺ₚ q holds as a proposition in its own right.
-/
noncomputable def iff_p (p q : Propn) : Propn :=
  conj (impl p q) (impl q p)

infixl:55 " ⟺ₚ " => iff_p

/--
  Double negation: ¬ₚ¬ₚp is intensionally identical to p.
-/
axiom neg_neg :
  ∀ p : Propn, neg (neg p) = p

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

/--
  Implication reduces to disjunction: p →ₚ q = ¬ₚp ∨ₚ q.

  This is the classical equivalence between material implication
  and disjunction, postulated at the intensional level.
-/
axiom impl_as_disj :
  ∀ p q : Propn, impl p q = disj (neg p) q

/--
  Conjunction is commutative at the propositional level.
-/
axiom conj_comm :
  ∀ p q : Propn, conj p q = conj q p

/--
  Disjunction is commutative at the propositional level.
-/
axiom disj_comm :
  ∀ p q : Propn, disj p q = disj q p

/--
  Conjunction is associative at the propositional level.
-/
axiom conj_assoc :
  ∀ p q r : Propn, conj (conj p q) r = conj p (conj q r)

/--
  Disjunction is associative at the propositional level.
-/
axiom disj_assoc :
  ∀ p q r : Propn, disj (disj p q) r = disj p (disj q r)

/--
  Biconditional is symmetric: if p ⟺ₚ q then q ⟺ₚ p.
-/
theorem iff_p_symm (p q : Propn) (h : p ⟺ₚ q) : q ⟺ₚ p := by
  unfold iff_p at *
  rw [conj_comm]
  rw [conj_comm] at h
  exact h

/--
  Double negation is involutive.
-/
theorem neg_neg_involutive (p : Propn) : neg (neg (neg (neg p))) = p := by
  rw [neg_neg, neg_neg]
