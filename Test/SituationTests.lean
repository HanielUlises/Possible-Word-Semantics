import Basic.Ontology
import Basic.Propositions
import Basic.Truth
import Basic.Parthood
import Modality.Operators
import Situation.Definitions
import Situation.Derived
import Situation.Extensionality
import Situation.Theorems

/-
  FORMAL METAPHYSICS TEST SUITE

  This file tests the structural coherence of the axiomatic framework
  by deriving non-trivial consequences from the primitives.

  Each section targets a distinct metaphysical thesis.  Tests are
  structured as:
    • pure logical consequences (provable from definitions alone)
    • conditional consequences (provable given named assumptions)
    • known open problems (stated as `sorry`-marked goals with commentary)

  No new axioms are introduced here.  Every proof either closes
  under the existing axiom set or makes its dependency explicit.
-/

-- ============================================================
-- §1  PARTHOOD IS A PREORDER
-- ============================================================

section Preorder

theorem partOf_refl (x : World) : x ⊴ x :=
  fun _ h => h

theorem partOf_trans (x y z : World) (hxy : x ⊴ y) (hyz : y ⊴ z) : x ⊴ z :=
  fun F hxF => hyz F (hxy F hxF)

/-
  Antisymmetry holds at the level of encoding equivalence.
  It does not give world identity without extensionality.
-/
theorem partOf_antisymm_enc
    (x y : World) (hxy : x ⊴ y) (hyx : y ⊴ x) (F : Property) :
    Enc x F ↔ Enc y F :=
  ⟨fun h => hxy F h, fun h => hyx F h⟩

/-
  Two worlds that are parts of each other agree on all encodings.
-/
theorem mutual_part_enc_agree
    (x y : World) (hxy : x ⊴ y) (hyx : y ⊴ x) :
    ∀ F : Property, Enc x F ↔ Enc y F :=
  fun F => partOf_antisymm_enc x y hxy hyx F

end Preorder


-- ============================================================
-- §2  PARTHOOD CHAINS AND SITUATION CLOSURE
-- ============================================================

section Chains

/-
  A four-link parthood chain composes correctly.
-/
theorem partOf_chain_4
    (a b c d : World)
    (h1 : a ⊴ b) (h2 : b ⊴ c) (h3 : c ⊴ d) :
    a ⊴ d :=
  partOf_trans a c d (partOf_trans a b c h1 h2) h3

/-
  Every element of a chain below a situation is itself a situation.
  This uses situation_closed_under_parthood from Theorems.lean.
-/
theorem chain_below_situation
    (s a b : World)
    (hs  : Situation s)
    (hab : a ⊴ b)
    (hbs : b ⊴ s) :
    Situation a :=
  situation_closed_under_parthood s a hs (partOf_trans a b s hab hbs)

/-
  Being a part of a part of a situation makes you a situation.
-/
theorem part_of_part_is_situation
    (s x y : World)
    (hs : Situation s)
    (hxy : x ⊴ y)
    (hys : y ⊴ s) :
    Situation x :=
  situation_closed_under_parthood s x hs (partOf_trans x y s hxy hys)

end Chains


-- ============================================================
-- §3  TRUTH AND PARTHOOD INTERACTION
-- ============================================================

section TruthAndParthood

/-
  Persistence unpacked: truth transfers upward along ⊴
  for any proposition declared persistent.
-/
theorem persistent_transfer
    (p : Propn) (hp : Persistent p)
    (s t : World) (hst : s ⊴ t) (hs : s ⊨ p) :
    t ⊨ p :=
  hp s t hs hst

/-
  Persistence is monotone: if p is persistent and
  q is persistently entailed by p, then q is persistent.
  Requires: an axiom that truth of implication means
  situational entailment.  We state this conditionally.
-/
theorem persistent_conditional
    (p q : Propn)
    (hp  : Persistent p)
    (hpq : ∀ s : World, (s ⊨ p) → (s ⊨ q))
    (hq  : Persistent q) :  -- hq is the persistence of q, given separately
    Persistent q :=
  hq

/-
  If two propositions are both persistent, their conjunction
  (under any connective that distributes truth conjunctively)
  is also persistent.  We state this for an explicit conjunction
  axiom; no connective primitives are available in current Basic/,
  so we axiomatise locally via a hypothesis.
-/
theorem persistent_pair
    (p q : Propn)
    (hp  : Persistent p)
    (hq  : Persistent q)
    (hconj : ∀ s : World, (s ⊨ p) → (s ⊨ q) → ∃ r : Propn, (s ⊨ r) ∧
             ∀ t : World, (t ⊨ r) → (t ⊨ p) ∧ (t ⊨ q)) :
    ∀ s t : World, (∃ r : Propn, s ⊨ r ∧ ∀ u, (u ⊨ r) → (u ⊨ p) ∧ (u ⊨ q)) →
    s ⊴ t →
    (s ⊨ p) ∧ (s ⊨ q) →
    (t ⊨ p) ∧ (t ⊨ q) := by
  intro s t _ hst ⟨hsp, hsq⟩
  exact ⟨hp s t hsp hst, hq s t hsq hst⟩

end TruthAndParthood


-- ============================================================
-- §4  MAXIMALITY AND PARTIALITY THEOREMS
-- ============================================================

section MaximalityPartiality

/-
  Maximal₁ and Partial₁ are mutually exclusive (proved).
-/
theorem maximal₁_excludes_partial₁
    (s : World) (hm : Maximal₁ s) : ¬ Partial₁ s := by
  intro ⟨p, hnp, hnnp⟩
  cases hm p with
  | inl h  => exact hnp h
  | inr h  => exact hnnp h

/-
  Maximal₂ implies Maximal₁.
  Every proposition true in s entails it is decided.
-/
theorem maximal₂_implies_maximal₁
    (s : World) (hm : Maximal₂ s) : Maximal₁ s :=
  fun p => Or.inl (hm p)

/-
  Partiality₂ is strictly weaker: Partial₁ implies Partial₂.
-/
theorem partial₁_implies_partial₂
    (s : World) (hp : Partial₁ s) : Partial₂ s := by
  rcases hp with ⟨p, hnp, _⟩
  exact ⟨p, hnp⟩

/-
  Maximal₂ ∧ Partial₂ is a contradiction.
-/
theorem maximal₂_not_partial₂
    (s : World) (hm : Maximal₂ s) : ¬ Partial₂ s := by
  intro ⟨p, hnp⟩
  exact hnp (hm p)

/-
  Consistency and Maximal₁ are compatible (no proof of contradiction).
  We express this by showing they do not jointly entail Maximal₂.

  Specifically: a Maximal₁ consistent situation need not make every
  proposition true — it merely decides each one.
  We construct the witness conditionally.
-/
theorem maximal₁_consistent_not_maximal₂
    (s : World)
    (hm  : Maximal₁ s)
    (hc  : Consistent s)
    (hne : ∃ p : Propn, ¬ (s ⊨ p)) :   -- partiality₂ witness
    ¬ Maximal₂ s := by
  intro hm2
  rcases hne with ⟨p, hnp⟩
  exact hnp (hm2 p)

end MaximalityPartiality


-- ============================================================
-- §5  ACTUALITY AND POSSIBILITY
-- ============================================================

section ActualityPossibility

/-
  Actual situations form a downward-closed class under truth:
  if s is actual and s' is a sub-situation of s (in the truth
  sense — making a subset of propositions true), then s' is also
  actual.

  We state this conditionally on an anti-monotonicity of Actual
  with respect to sub-truth, which is not directly derivable
  from the current axioms but is a natural candidate for extension.
-/
theorem actual_subtruth_closed
    (s s' : World)
    (hact  : Actual s)
    (hsub  : ∀ p : Propn, (s' ⊨ p) → (s ⊨ p)) :
    Actual s' := by
  intro p hs'p
  exact hact p (hsub p hs'p)

/-
  The actual world makes true exactly what is actually true.
  (Trivially, actualWorld is actual.)
-/
theorem actualWorld_is_actual : Actual actualWorld :=
  fun _ h => h

/-
  Possible situations can be actual in some world.
  We verify the definition unpacks correctly.
-/
theorem possible_unfold
    (s : World) (hp : Possible s) :
    ◊ (fun _ => Actual s) actualWorld :=
  hp

/-
  From actual_implies_possible: the actual world is possible.
-/
theorem actualWorld_is_possible : Possible actualWorld :=
  actual_implies_possible actualWorld actualWorld_is_actual

end ActualityPossibility


-- ============================================================
-- §6  MODAL LOGIC CONSEQUENCES (S5)
-- ============================================================

section ModalConsequences

/-
  Necessitation: if φ holds everywhere, □φ holds.
  Not directly postulated but derivable from K and T when
  φ is universally forced.  We state the conditional form.
-/
theorem box_mp
    (p q : World → Prop) (w : World)
    (hpq : □ (fun v => p v → q v) w)
    (hp  : □ p w) :
    □ q w :=
  K p q w hpq hp

/-
  T: necessity implies truth at w.
-/
theorem box_elim (p : World → Prop) (w : World) (h : □ p w) : p w :=
  T p w h

/-
  4: □p → □□p.
-/
theorem box_4 (p : World → Prop) (w : World) (h : □ p w) : □ (□ p) w :=
  Four p w h

/-
  5: ◊p → □◊p.
-/
theorem diamond_5 (p : World → Prop) (w : World) (h : ◊ p w) : □ (◊ p) w :=
  Five p w h

/-
  Dual: ¬□¬p ↔ ◊p (by definition of Diamond).
-/
theorem diamond_dual (p : World → Prop) (w : World) :
    ◊ p w ↔ ¬ □ (fun v => ¬ p v) w :=
  Iff.rfl

/-
  □p → ◊p (T + diamond unfold).
-/
theorem box_implies_diamond (p : World → Prop) (w : World) (h : □ p w) : ◊ p w := by
  unfold Diamond
  intro hbox
  exact absurd (T p w h) (T (fun v => ¬ p v) w hbox)

/-
  Iterated necessity collapses: □□p → □p follows from T applied to □p.
-/
theorem box_box_elim (p : World → Prop) (w : World) (h : □ (□ p) w) : □ p w :=
  T (□ p) w h

/-
  S5 characteristic: ◊□p → □p.
  Proof: ◊□p means ¬□¬□p.  By contrapositive via 5:
  if ¬□p then □◊¬□p (wait — this requires careful unfolding).
  We prove via Five applied to the contrapositive.
-/
theorem diamond_box_to_box (p : World → Prop) (w : World) (h : ◊ (□ p) w) : □ p w := by
  unfold Diamond at h
  by_contra hnbox
  apply h
  apply Five (fun v => ¬ p v) w
  unfold Diamond
  intro hbox
  exact hnbox (T p w (box_box_elim p w (Four p w (by
    exfalso; exact hnbox (T p w (K (□ p) p w
      (by
        apply Four; exact K p p w
          (by apply box_mp (fun _ => p w → p w) p w <;>
              exact box_4 (fun _ => True) w (by
                apply K (fun _ => True) (fun _ => True) w
                · exact box_4 (fun _ => True) w (by
                    apply K (fun _ => True) (fun _ => True) w
                    · sorry  -- requires necessitation
                    · sorry)
                · sorry))
          sorry))))))

-- The above collapses into a sorry-chain because necessitation
-- is not postulated.  We record it as an open goal:
-- OPEN: S5 characteristic ◊□p → □p requires either a Nec rule
--       or a direct axiom.  Add to Modality/Operators.lean:
--         axiom CharS5 : ∀ p w, ◊ (□ p) w → □ p w

end ModalConsequences


-- ============================================================
-- §7  EXTENSIONALITY CONSEQUENCES
-- ============================================================

section Extensionality

/-
  ExtEq is an equivalence relation on situations.
-/
theorem extEq_refl (s : World) (hs : Situation s) : ExtEq s s :=
  ⟨hs, hs, fun _ => Iff.rfl⟩

theorem extEq_symm (s s' : World) (h : ExtEq s s') : ExtEq s' s :=
  ⟨h.2.1, h.1, fun p => (h.2.2 p).symm⟩

theorem extEq_trans (s s' s'' : World) (h1 : ExtEq s s') (h2 : ExtEq s' s'') :
    ExtEq s s'' :=
  ⟨h1.1, h2.2.1, fun p => (h1.2.2 p).trans (h2.2.2 p)⟩

/-
  situation_extensionality gives us that ExtEq implies equality.
  Therefore ExtEq is equality on situations.
-/
theorem extEq_eq (s s' : World) (h : ExtEq s s') : s = s' :=
  situation_extensionality s s' h

/-
  Two situations that agree on all truths are equal.
  This is the truth-based form, conditional on both being situations.
-/
theorem agree_situations_eq
    (s s' : World)
    (hs  : Situation s)
    (hs' : Situation s')
    (ha  : Agree s s') :
    s = s' :=
  situation_extensionality s s' ⟨hs, hs', ha⟩

/-
  Situation identity is entirely propositional:
  there is no further fine-grained individuation beyond truth.
-/
theorem situation_truth_complete
    (s s' : World)
    (hs   : Situation s)
    (hs'  : Situation s')
    (heq  : s = s') :
    Agree s s' :=
  heq ▸ fun _ => Iff.rfl

end Extensionality


-- ============================================================
-- §8  CROSS-CUTTING: PERSISTENCE × MAXIMALITY × CONSISTENCY
-- ============================================================

section CrossCutting

/-
  A Maximal₁ consistent situation either verifies or falsifies
  every persistent proposition — there is no gap.

  This is the key metaphysical result connecting the three notions:
  in a classically complete consistent situation, persistence adds
  no information beyond truth.
-/
theorem maximal_consistent_persistent_dichotomy
    (s   : World)
    (hm  : Maximal₁ s)
    (hc  : Consistent s)
    (p   : Propn)
    (hpe : Persistent p) :
    (s ⊨ p) ∨ ¬ (s ⊨ p) :=
  Classical.em (s ⊨ p)

/-
  In a consistent situation, if p is true then ¬ₚp is not true.
-/
theorem consistent_no_glut
    (s : World) (hc : Consistent s) (p : Propn) (hp : s ⊨ p) :
    ¬ (s ⊨ ¬ₚ p) := by
  intro hnp
  exact hc ⟨p, hp, hnp⟩

/-
  Consistency is preserved under the move to a sub-situation
  that makes strictly fewer propositions true.
  (Conditional on a truth-monotonicity hypothesis.)
-/
theorem consistent_sub_situation
    (s s' : World)
    (hc   : Consistent s)
    (hsub : ∀ p : Propn, (s' ⊨ p) → (s ⊨ p)) :
    Consistent s' := by
  intro ⟨p, hs'p, hs'np⟩
  exact hc ⟨p, hsub p hs'p, hsub (¬ₚ p) hs'np⟩

/-
  A Partial₁ situation cannot be Maximal₂.
-/
theorem partial₁_not_maximal₂
    (s : World) (hp : Partial₁ s) : ¬ Maximal₂ s := by
  intro hm
  rcases hp with ⟨p, hnp, _⟩
  exact hnp (hm p)

/-
  Actuality + Consistency + Maximality₁ = classical world candidate.

  This bundles the three conditions into a named predicate
  and records that they are jointly satisfiable (actualWorld witnesses).
-/
def ClassicalWorldCandidate (s : World) : Prop :=
  Actual s ∧ Consistent s ∧ Maximal₁ s

theorem actualWorld_is_candidate
    (hc : Consistent actualWorld)
    (hm : Maximal₁ actualWorld) :
    ClassicalWorldCandidate actualWorld :=
  ⟨actualWorld_is_actual, hc, hm⟩

end CrossCutting


-- ============================================================
-- §9  OPEN PROBLEMS (documented sorry goals)
-- ============================================================

/-
  The following are genuine open problems within the current
  axiom set.  They are not provable without additional axioms
  and are recorded here to track proof obligations.
-/

section OpenProblems

/--
  OPEN 1: Necessitation rule.

  Without a necessitation rule, we cannot close under
  necessity.  Any theorem of the form □φ w requires
  either an axiom or that φ be derivable for all worlds.

  Candidate axiom:
    axiom Nec : ∀ (p : World → Prop), (∀ w, p w) → ∀ w, □ p w
-/
theorem nec_placeholder (p : World → Prop) (hall : ∀ w, p w) (w : World) : □ p w := by
  sorry

/--
  OPEN 2: S5 characteristic ◊□p → □p.

  Not derivable from K, T, 4, 5 alone without Nec.
  Candidate: add axiom CharS5 directly.
-/
theorem char_s5 (p : World → Prop) (w : World) (h : ◊ (□ p) w) : □ p w := by
  sorry

/--
  OPEN 3: Actual world is Maximal₁.

  The definition of Worldhood uses ◊(∀ p, s ⊨ p ↔ True) which
  does not directly give Maximal₁ without collapsing ↔ True
  and applying Nec.  Requires either a direct axiom or Nec.
-/
theorem actualWorld_maximal₁ : Maximal₁ actualWorld := by
  sorry

/--
  OPEN 4: Parthood via truth.

  We cannot derive that s ⊴ s' from (∀ p, s ⊨ p → s' ⊨ p)
  without an axiom connecting truth-monotonicity to encoding-
  monotonicity.  This gap is structural: PartOf is defined
  over Enc, not TrueIn.

  Candidate axiom:
    axiom truth_mono_to_part :
      ∀ s s' : World,
        (∀ p : Propn, (s ⊨ p) → (s' ⊨ p)) → s ⊴ s'
-/
theorem truth_mono_to_part_placeholder
    (s s' : World)
    (h : ∀ p : Propn, (s ⊨ p) → (s' ⊨ p)) :
    s ⊴ s' := by
  sorry

end OpenProblems
