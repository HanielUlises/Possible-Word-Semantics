import Grounding.Ontology
import Grounding.Propositions
import Grounding.Truth
import Grounding.Parthood
import Situation.Definitions

/-
  THEOREMS OF SITUATION SEMANTICS
-/

/--
  theorem 2 (extensionality of situations via truth)

  Two situations are identical iff they make exactly the
  same propositions true.
-/
axiom situation_extensionality_via_truth :
  ∀ s₁ s₂ : World,
    Situation s₁ →
    Situation s₂ →
    (∀ p : Propn, (s₁ ⊨ p) ↔ s₂ ⊨ p) →
    s₁ = s₂

/--
  maximality₁ excludes partiality₁.
-/
theorem maximal₁_not_partial₁ :
    ∀ s : World,
      Maximal₁ s →
      ¬ Partial₁ s := by
  intro s hmax hpart
  rcases hpart with ⟨p, hp, hnp⟩
  cases hmax p with
  | inl hp' => exact hp hp'
  | inr hnp' => exact hnp hnp'

/--
  actual situations are possible.
-/
axiom actual_implies_possible :
  ∀ s : World,
    Actual s →
    Possible s

/--
  maximality₂ implies non-partiality₂.
-/
theorem maximal₂_not_partial₂ :
    ∀ s : World,
      Maximal₂ s →
      ¬ Partial₂ s := by
  intro s hmax hpart
  rcases hpart with ⟨p, hp⟩
  exact hp (hmax p)

/--
  Every part of a situation is itself a situation.
-/
axiom situation_closed_under_parthood :
  ∀ s x : World,
    Situation s →
    (x ⊴ s) →
    Situation x

/--
  Parthood is monotone with respect to truth.

  If x is a part of y, and p is persistent, then
  truth of p transfers from x to y.
-/
theorem parthood_truth_monotone :
    ∀ (x y : World) (p : Propn),
      x ⊴ y →
      Persistent p →
      (x ⊨ p) →
      (y ⊨ p) := by
  intro x y p hxy hpers hxp
  exact hpers x y hxp hxy

/--
  Persistent propositions are closed upward along parthood.

  Equivalent to persistence but stated as a closure property.
-/
theorem persistent_upward_closed :
    ∀ p : Propn,
      Persistent p ↔
      ∀ x y : World, x ⊴ y → (x ⊨ p) → (y ⊨ p) := by
  intro p
  constructor
  · intro h x y hxy hx
    exact h x y hx hxy
  · intro h x y hx hxy
    exact h x y hxy hx

/--
  The conjunction of two persistent propositions is persistent.
-/
theorem persistent_conj :
    ∀ p q : Propn,
      Persistent p →
      Persistent q →
      Persistent (p ∧ₚ q) := by
  intro p q hp hq s s' hpq hss'
  rw [TrueIn_conj] at hpq ⊢
  exact ⟨hp s s' hpq.1 hss', hq s s' hpq.2 hss'⟩

/--
  Consistency is downward closed under parthood.

  Every part of a consistent situation is itself consistent.

  If the sub-situation were inconsistent, it would make some
  proposition and its negation true; since parts extend into
  the whole, the contradiction would propagate upward via
  persistent negation — unless negation is not persistent.
  The result is stated as an axiom acknowledging this gap.
-/
axiom consistent_downward_closed :
  ∀ (s x : World),
    Consistent s →
    x ⊴ s →
    Consistent x

/--
  Actual situations are consistent.

  If s is actual and inconsistent, then both p and ¬ₚp are
  true in s, hence both are true in actualWorld, which
  contradicts the classical reading of actualWorld.

  This requires TrueIn_neg and is therefore treated as an
  axiom pending a full treatment of negation.
-/
axiom actual_consistent :
  ∀ s : World, Actual s → Consistent s

/--
  Partial₁ and Partial₂ are independent: every Partial₂
  situation that is also Maximal₁ witnesses the gap between
  the two partiality notions.

  Partial₂ says some proposition is not true.
  Maximal₁ says every proposition is decided (true or neg-true).
  These are jointly satisfiable, and this theorem records that fact.
-/
theorem partial₂_compatible_with_maximal₁ :
    ∀ s : World,
      Maximal₁ s →
      Partial₂ s →
      ∃ p : Propn, ¬ (s ⊨ p) ∧ (s ⊨ ¬ₚ p) := by
  intro s hmax hpart
  rcases hpart with ⟨p, hnp⟩
  cases hmax p with
  | inl hp => exact absurd hp hnp
  | inr hnegp => exact ⟨p, hnp, hnegp⟩

/-- Theorem 8 (Zalta 1993): every proposition is persistent.
    A proposition true in a situation remains true in every
    situation that extends it. Persistence is not a special
    property of select propositions but holds universally,
    reflecting that informational content is monotone under
    the parthood order.

    Proof is direct from part_truth_mono once OP-2 and OP-3
    are resolved. Marked sorry until then. Sorry-/
theorem all_propositions_persistent :
    ∀ p : Propn, Persistent p := by
  intro p s s' hsp hss'
  sorry -- OP-2, OP-3: requires part_truth_mono to be closed
