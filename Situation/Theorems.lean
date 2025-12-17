import Basic.Ontology
import Basic.Propositions
import Basic.Truth
import Basic.Parthood
import Situation.Definitions

/-
  THEOREMS OF SITUATION SEMANTICS

  This section formulates general results concerning situations
  within the present axiomatic framework.

  No new ontological primitives are introduced here.  All claims
  are expressed solely in terms of the previously fixed notions
  of world, situation, propositional truth, parthood, and modality.

  Some principles are logical consequences of the definitions
  already given and are established by proof.

  Others express substantive extensional or identity conditions
  for situations.  These correspond to metatheoretic results
  (for example, theorem 2 as established in an external first-order
  proof system) and are therefore recorded as axioms rather than
  derived internally.
-/

/--
  theorem 2 (extensionality of situations via truth)

  Two situations are identical iff they make exactly the
  same propositions true.

  This principle expresses the extensional individuation
  of situations by propositional content.

  This theorem is not derivable from the purely intensional
  primitives alone; it corresponds to theorem 2 proven
  externally in Prover9 and is therefore postulated here.
-/
axiom situation_extensionality_via_truth :
  ∀ s₁ s₂ : World,
    Situation s₁ →
    Situation s₂ →
    (∀ p : Propn, s₁ ⊨ p ↔ s₂ ⊨ p) →
    s₁ = s₂

/--
  maximality₁ excludes partiality₁

  A situation that decides every proposition cannot
  leave any proposition undetermined.

  This result follows directly from the definitions.
-/
theorem maximal₁_not_partial₁ :
  ∀ s : World,
    Maximal₁ s →
    ¬ Partial₁ s :=
by
  intro s hmax hpart
  unfold Partial₁ at hpart
  rcases hpart with ⟨p, hp, hnp⟩
  unfold Maximal₁ at hmax
  cases hmax p with
  | inl hp' => exact hp hp'
  | inr hnp' => exact hnp hnp'

/--
  actual situations are possible

  This is immediate from the definition of possibility.
-/
theorem actual_implies_possible :
  ∀ s : World,
    Actual s →
    Possible s :=
by
  intro s h
  unfold Possible
  exact ⟨_, h⟩

/--
  maximality₂ implies non-partiality₂

  If every proposition is true in a situation, then
  there exists no proposition that fails to be true.
-/
theorem maximal₂_not_partial₂ :
  ∀ s : World,
    Maximal₂ s →
    ¬ Partial₂ s :=
by
  intro s hmax hpart
  unfold Partial₂ at hpart
  rcases hpart with ⟨p, hp⟩
  unfold Maximal₂ at hmax
  exact hp (hmax p)
