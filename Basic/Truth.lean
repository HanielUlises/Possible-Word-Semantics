import Basic.Ontology
import Basic.Propositions

/-
  TRUTH IN SITUATIONS

  Truth-in is constrained by axioms connecting it to
  propositional encoding via properties, following the
  Prover9 axiomatization used in the metatheoretic proofs.
-/

/--
  Truth of a proposition in a situation (or world).
-/
axiom TrueIn : World → Propn → Prop

notation:30 x " ⊨ " p => TrueIn x p

/--
  Propositional encoding via properties.

  A proposition p is encoded in an object x iff there exists
  a property F such that F = VAC p and x encodes F.
-/
axiom Encp_def :
  ∀ x : World, ∀ p : Propn,
    Object x →
      (Encp x p ↔
        ∃ F : Property, F = VAC p ∧ Enc x F)

/--
  Truth reduces to propositional encoding.
-/
axiom TrueIn_def :
  ∀ x : World, ∀ p : Propn,
    Object x →
      ((x ⊨ p) ↔ Encp x p)

/--
  Truth of a conjunction: s ⊨ p ∧ₚ q ↔ s ⊨ p ∧ s ⊨ q.
-/
axiom TrueIn_conj :
  ∀ (s : World) (p q : Propn),
    (s ⊨ p ∧ₚ q) ↔ (s ⊨ p) ∧ (s ⊨ q)

/--
  Truth of a disjunction: s ⊨ p ∨ₚ q ↔ s ⊨ p ∨ s ⊨ q.
-/
axiom TrueIn_disj :
  ∀ (s : World) (p q : Propn),
    (s ⊨ p ∨ₚ q) ↔ (s ⊨ p) ∨ (s ⊨ q)

/--
  Truth of implication: s ⊨ p →ₚ q ↔ (s ⊨ p → s ⊨ q).

  NB: this makes material implication match situational
  implication, which is a deliberate strong choice.
-/
axiom TrueIn_impl :
  ∀ (s : World) (p q : Propn),
    (s ⊨ p →ₚ q) ↔ ((s ⊨ p) → (s ⊨ q))

/--
  Truth of negation: s ⊨ ¬ₚp ↔ ¬(s ⊨ p).
-/
axiom TrueIn_neg :
  ∀ (s : World) (p : Propn),
    (s ⊨ ¬ₚ p) ↔ ¬(s ⊨ p)
