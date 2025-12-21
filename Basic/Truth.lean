import Basic.Ontology
import Basic.Propositions

/-
  truth in situations.

  truth is reduced to propositional encoding,
  following the prover9 axiomatization.
-/

/--
  truth of a proposition in an object.
-/
axiom TrueIn : Propn → World → Prop

notation:50 p " ⊨ " x => TrueIn p x

/-
  axioms connecting truth, propositions, and encoding.
-/

/--
  propositional encoding via properties.

  corresponds to:
  Encp(x,p) <-> ∃F(Property(F) & F = VAC(p) & Enc(x,F))
-/
axiom Encp_def :
  ∀ x : World, ∀ p : Propn,
    Object x →
      (Encp x p ↔
        ∃ F : Property, F = VAC p ∧ Enc x F)

/--
  truth reduces to propositional encoding.
-/
axiom TrueIn_def :
  ∀ x : World, ∀ p : Propn,
    Object x →
      ((p ⊨ x) ↔ Encp x p)
