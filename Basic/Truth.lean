import Basic.Ontology
import Basic.Propositions

/-
  TRUTH IN SITUATIONS

  This theory introduces truth-in as a primitive relation
  between situations (or worlds) and propositions.

  Truth is not taken as fundamental in isolation, but is
  constrained by axioms connecting it to propositional
  encoding via properties, following the Prover9
  axiomatization used in the metatheoretic proofs.

  The orientation of truth is world-first:
    s ⊨ p
  in accordance with standard situation and Kripke semantics.
-/

/--
  Truth of a proposition in a situation (or world).
-/
axiom TrueIn : World → Propn → Prop

notation:50 s " ⊨ " p => TrueIn s p

/-
  AXIOMS CONNECTING TRUTH, PROPOSITIONS, AND ENCODING
-/

/--
  Propositional encoding via properties.

  A proposition p is encoded in an object x iff there exists
  a property F such that:
    • F is the vacuous abstraction of p, and
    • x encodes F.

  Corresponds exactly to the Prover9 axiom:

    Encp(x,p) ↔ ∃F (Property(F) ∧ F = VAC(p) ∧ Enc(x,F))
-/
axiom Encp_def :
  ∀ x : World, ∀ p : Propn,
    Object x →
      (Encp x p ↔
        ∃ F : Property, F = VAC p ∧ Enc x F)

/--
  Truth reduces to propositional encoding.

  A proposition is true in a situation iff that situation
  propositionally encodes it.

  Corresponds exactly to the Prover9 axiom:

    TrueIn(p,x) ↔ Encp(x,p)
-/
axiom TrueIn_def :
  ∀ x : World, ∀ p : Propn,
    Object x →
      (x ⊨ p ↔ Encp x p)
