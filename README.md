# Possible-World-Semantics

A formal development of possible-world and situation semantics in Lean 4, following the higher-order modal and situation-theoretic tradition of Zalta, Fine, and Barwise–Perry.

All ontological primitives are taken as axioms. Every defined notion is built from them without appeal to set theory or Mathlib. Metatheoretic results proven externally in Prover9 are recorded as axioms with explicit documentation of the proof obligation.

---

## Theoretical Background

The development follows the Zalta–Fine tradition, in which worlds and situations are not distinguished at the type level. `World` is the single domain; `Situation` and `Object` are predicates over it, not separate types.

The central primitive is encoding (`Enc`). A situation encodes the properties that constitute its informational content. Parthood is defined encoding-first: `s ⊴ s'` holds iff every property encoded by `s` is also encoded by `s'`, which matches the mereology of informational situations in Barwise–Perry and the abstract object theory of Zalta.

Modal operators are axiomatic rather than reduced to Kripke frames. The S5 schemas are postulated directly:

□(φ → ψ) → □φ → □ψ        (K)

□φ → φ                      (T)

□φ → □□φ                    (4)

◊φ → □◊φ                    (5)


`Modality/Frames.lean` provides the corresponding frame-level conditions — reflexivity, transitivity, and symmetry of the accessibility relation R — as a potential semantic grounding, but these are not wired to `Box` by default. The modal strength of the system is fixed axiomatically, leaving the surrounding theory of situations neutral with respect to frame semantics.

Extensionality is a postulate (not a theorem). Situations are individuated by propositional content according to the principle:

```math
Situation(s) ∧ Situation(s') ∧ (∀p, s ⊨ p ↔ s' ⊨ p) → s = s'
```

This cannot be derived from purely intensional primitives and must be stipulated, matching the standard move in both situation semantics and abstract object theory.

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
| `Nec` | `Modality/Operators` | necessitation rule |
| `PossNec` | `Modality/Operators` | ◊□φ → □φ, S5 collapse |
| `actualWorld` | `Situation/Definitions` | designated constant |
| `situation_extensionality` | `Situation/Extensionality` | constitutive postulate |
| `situation_extensionality_via_truth` | `Situation/Theorems` | Prover9 Theorem 2 |
| `actual_implies_possible` | `Situation/Theorems` | modal postulate |
| `situation_closed_under_parthood` | `Situation/Theorems` | Prover9 Theorem 3 |

---

## Open Proof Obligations

These are genuine gaps in the axiom inventory. Each one blocks one or more theorems downstream. They are marked with `sorry` in the source and tracked here until resolved.

Every `sorry` in this codebase corresponds to exactly one entry in this table. No `sorry` is left without a corresponding open problem entry.

| ID | Obligation | Blocks | File |
|---|---|---|---|
| OP-2 | `truth_mono_to_part` | `parthood_iff_truth_inclusion` (←), Theorems 4–6 | `Basic/Parthood.lean` |
| OP-3 | `situation_is_object` | `part_truth_mono`, all theorems applying `TrueIn_def` to a situation | `Basic/Ontology.lean` |

### OP-2 — Parthood via truth-monotonicity

`PartOf` is defined over `Enc` while `TrueIn` is an independent primitive. There is no axiom in the current inventory connecting the two orderings. The direction

```
(∀p, s ⊨ p → s' ⊨ p) → s ⊴ s'
```

is therefore not derivable, leaving the biconditional

```
Situation(s) ∧ Situation(s') → (s ⊴ s' ↔ ∀p, s ⊨ p → s' ⊨ p)
```

half-proved. This blocks the antisymmetry of parthood (Theorem 5, Zalta 1993):

```
Situation(s) ∧ Situation(s') ∧ s ⊴ s' ∧ s' ⊴ s → s = s'
```

and the same-parts identity principle (Theorem 6, Zalta 1993):

```
Situation(s) ∧ Situation(s') ∧ (∀s'', s'' ⊴ s ↔ s'' ⊴ s') → s = s'
```

both of which depend on the full equivalence. Metatheoretic justification: Prover9 proof in `theorem4.in` at peoppenheimer.org/cm/worlds/, corresponding to Theorem 4 of Zalta (1993).

```lean
axiom truth_mono_to_part :
  ∀ s s' : World, (∀ p : Propn, s ⊨ p → s' ⊨ p) → s ⊴ s'
```

### OP-3 — Situations are objects

`TrueIn_def` and `Encp_def` both carry an `Object x` hypothesis. `Situation` and `Object` are independent predicates in `Basic/Ontology.lean` and nothing in the current inventory forces their extensions to overlap. Any theorem that evaluates truth inside a situation therefore requires the bridge

```
Situation(s) → Object(s)
```

as an additional premise. In Zalta's abstract object theory this inclusion is constitutive: situations are a species of abstract object and the predicate inclusion holds by definition. It must be postulated explicitly here because `Object` and `Situation` are both taken as primitive.

```lean
axiom situation_is_object : ∀ s : World, Situation s → Object s
```

---

## Resolved Proof Obligations

### OP-1 — Necessitation and possible-necessity collapse

The necessitation rule `(∀w, φw) → ∀w, □φw` and the S5 collapse `◊□φ → □φ` were not derivable from K, T, 4, and 5 alone. Necessitation is admissible in every normal modal logic but is not a substitution instance of any of the four schemas. The collapse `◊□φ → □φ` holds in all S5 frames by the euclidean character of the accessibility relation but requires either a frame-level reduction or a direct postulate in a purely axiomatic development.

Both were closed by postulating `Nec` and `PossNec` in `Modality/Operators.lean`. The alternative — deriving them from `Modality/Frames.lean` — remains available but is not imposed, preserving the neutrality of the modal layer with respect to frame semantics.

---

## References

Zalta, E. *Intensional Logic and the Metaphysics of Intentionality*. MIT Press, 1988.

Fine, K. "Ontological Dependence." *Proceedings of the Aristotelian Society*, 1995.

Barwise, J. & Perry, J. *Situations and Attitudes*. MIT Press, 1983.

Oppenheimer, P. & Zalta, E. "The Computational Theory of Possible Worlds." peoppenheimer.org/cm/worlds/
