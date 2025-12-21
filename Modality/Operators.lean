import Basic.Ontology

/-
  Modal operator and axioms (S5)

  This development introduces a minimal modal vocabulary
  together with axioms characterizing S5 modal logic.

  No semantic reduction (e.g. to Kripke frames) is imposed here.
  Instead, modal strength is fixed axiomatically, allowing the
  surrounding theory of situations to remain neutral.

  Modal operators are therefore treated as primitive but governed
  by explicit principles.
-/

/--
  Necessity operator.

  □ p is read as: p holds at all admissible worlds.
-/
axiom Box : (World → Prop) → World → Prop

/--
  Possibility operator.

  ◊ p is defined as the dual of necessity.
-/
def Diamond (p : World → Prop) : World → Prop :=
  fun w => ¬ Box (fun v => ¬ p v) w

notation "□" => Box
notation "◊" => Diamond

/-
  S5 axioms

  These axioms characterize the modal logic S5:
  necessity is reflexive, transitive, symmetric,
  and insensitive to world identity.
-/

/--
  Axiom K (distribution).

  Necessity distributes over implication.
-/
axiom K :
  ∀ (p q : World → Prop) (w : World),
    □ (fun v => p v → q v) w →
    □ p w →
    □ q w

/--
  Axiom T (reflexivity).

  What is necessary is the case.
-/
axiom T :
  ∀ (p : World → Prop) (w : World),
    □ p w → p w

/--
  Axiom 4 (positive introspection).

  What is necessary is necessarily necessary.
-/
axiom Four :
  ∀ (p : World → Prop) (w : World),
    □ p w → □ (□ p) w

/--
  Axiom 5 (negative introspection).

  What is possible is necessarily possible.
-/
axiom Five :
  ∀ (p : World → Prop) (w : World),
    ◊ p w → □ (◊ p) w
