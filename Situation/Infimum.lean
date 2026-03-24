import Grounding.Ontology
import Grounding.Truth
import Grounding.Parthood
import Situation.Definitions

/-
  INFIMUM (MEET) OF SITUATIONS

  The meet of two situations is the largest situation
  that is a part of both.  Since situations are individuated
  by their propositional content (via extensionality), the
  meet is characterised by the propositions true in both.

  This is the situation-semantic analogue of set-theoretic
  intersection restricted to the situational domain.
-/

/--
  The meet of s and s' is a world that makes exactly the
  propositions true that are true in both s and s'.

  Its existence is not derivable from the primitives alone
  and is therefore postulated.
-/
axiom meet : World → World → World

/--
  The meet makes precisely the shared truths true.
-/
axiom TrueIn_meet :
  ∀ (s s' : World) (p : Propn),
    (meet s s' ⊨ p) ↔ ((s ⊨ p) ∧ (s' ⊨ p))

/--
  The meet is a part of its left argument.
-/
theorem meet_le_left :
    ∀ (s s' : World), meet s s' ⊴ s := by
  intro s s' F hF
  sorry

/--
  The meet is a part of its right argument.
-/
theorem meet_le_right :
    ∀ (s s' : World), meet s s' ⊴ s' := by
  intro s s' F hF
  sorry

/--
  Any common lower bound is a part of the meet.

  If x is a part of both s and s', then x is a part of
  meet s s'.  This makes meet the greatest lower bound.
-/
theorem meet_greatest :
    ∀ (x s s' : World),
      x ⊴ s → x ⊴ s' → x ⊴ meet s s' := by
  intro x s s' _hxs _hxs' F hxF
  sorry

/--
  The meet of a situation with itself is itself.
-/
theorem meet_self :
    ∀ s : World,
      Situation s →
      meet s s = s := by
  intro s hs
  apply situation_extensionality_via_truth _ _ hs
  · apply situation_closed_under_parthood s
    · exact hs
    · intro F hF
      exact (TrueIn_meet s s _).mpr ⟨hF, hF⟩ |>.left |>.elim (fun h => h) (fun h => h)
  · intro p
    constructor
    · intro h
      exact ((TrueIn_meet s s p).mp h).1
    · intro h
      exact (TrueIn_meet s s p).mpr ⟨h, h⟩

/--
  The meet is commutative up to situational identity.
-/
theorem meet_comm :
    ∀ s s' : World,
      Situation s → Situation s' →
      meet s s' = meet s' s := by
  intro s s' hs hs'
  apply situation_extensionality_via_truth
  · apply situation_closed_under_parthood s
    · exact hs
    · intro F hF; exact ((TrueIn_meet s s' _).mp hF).1 |>.elim id id
  · apply situation_closed_under_parthood s'
    · exact hs'
    · intro F hF; exact ((TrueIn_meet s' s _).mp hF).1 |>.elim id id
  · intro p
    simp only [TrueIn_meet]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1⟩
