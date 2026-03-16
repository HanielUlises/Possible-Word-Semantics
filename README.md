# Possible-Word-Semantics

A formal development of possible-world and situation semantics in Lean 4, following the higher-order modal and situation-theoretic tradition of Zalta, Fine, and Barwise–Perry.

All ontological primitives are taken as axioms. Every defined notion is built from them without appeal to set theory or Mathlib. Metatheoretic results proven externally in Prover9 are recorded as axioms with explicit documentation of the proof obligation.

---

## Theoretical Background

The development follows the **Zalta–Fine** tradition:

- **Worlds and situations** are not distinguished at the type level. `World` is the single domain; `Situation` and `Object` are predicates over it.
- **Encoding** (`Enc`) is the central primitive, not predication. A situation *encodes* the properties that constitute its informational content.
- **Parthood** is defined encoding-first: `s ⊴ s'` iff every property encoded by `s` is also encoded by `s'`. This matches the mereology of informational situations in Barwise–Perry and the abstract object theory of Zalta.
- **Modal operators** are axiomatic (S5), not reduced to Kripke frames. `Modality/Frames.lean` provides the frame-level conditions separately as a potential semantic interpretation; they are not wired to `Box` by default.
- **Extensionality** is a postulate, not a theorem. Situations are individuated by propositional content, but this cannot be derived from purely intensional primitives — it must be stipulated, matching the standard move in both situation semantics and abstract object theory.

---

## Axiom Inventory

| Axiom | File | Status |
|---|---|---|
| `World`, `Property`, `Propn` | `Basic/Ontology` | primitive type |
| `Object`, `Situation` | `Basic/Ontology` | primitive predicate |
| `Enc`, `Encp`, `VAC` | `Basic/Ontology` | primitive relation / operator |
| `neg` (¬ₚ) | `Basic/Propositions` | primitive connective |
| `TrueIn` (⊨) | `Basic/Truth` | primitive relation |
| `Encp_def` | `Basic/Truth` | Prover9-verified metatheorem |
| `TrueIn_def` | `Basic/Truth` | Prover9-verified metatheorem |
| `R`, `R_refl`, `R_trans`, `R_symm` | `Modality/Frames` | S5 frame conditions |
| `Box` (□) | `Modality/Operators` | primitive modal operator |
| `K`, `T`, `Four`, `Five` | `Modality/Operators` | S5 axioms |
| `actualWorld` | `Situation/Definitions` | designated constant |
| `situation_extensionality` | `Situation/Extensionality` | constitutive postulate |
| `situation_extensionality_via_truth` | `Situation/Theorems` | Prover9 Theorem 2 |
| `actual_implies_possible` | `Situation/Theorems` | modal postulate |
| `situation_closed_under_parthood` | `Situation/Theorems` | Prover9 Theorem 3 |

---

## Open Problems

These are genuine proof obligations that require additional axioms not yet in the theory.

**Necessitation** — the rule `(∀ w, p w) → ∀ w, □ p w` is not postulated. Without it, no theorem of the form `□φ w` is derivable from universal facts alone. This blocks the S5 characteristic `◊□p → □p` and the derivation that `actualWorld` is `Maximal₁`.

Candidate axiom to add to `Modality/Operators.lean`:
```lean
axiom Nec : ∀ (p : World → Prop), (∀ w, p w) → ∀ w, □ p w
```

**Parthood via truth-monotonicity** — `PartOf` is defined over `Enc`, while `TrueIn` is a separate primitive. There is no axiom connecting truth-monotonicity to encoding-monotonicity, so `(∀ p, s ⊨ p → s' ⊨ p) → s ⊴ s'` is not derivable.

Candidate axiom to add to `Basic/Parthood.lean`:
```lean
axiom truth_mono_to_part :
  ∀ s s' : World, (∀ p : Propn, (s ⊨ p) → (s' ⊨ p)) → s ⊴ s'
```

---

## References

- Zalta, E. *Intensional Logic and the Metaphysics of Intentionality*. MIT Press, 1988.
- Fine, K. "Ontological Dependence." *Proceedings of the Aristotelian Society*, 1995.
- Barwise, J. & Perry, J. *Situations and Attitudes*. MIT Press, 1983.