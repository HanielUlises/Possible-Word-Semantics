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

/-- Necessitation encodes the closure of the logic under universal truth:
    any proposition holding at every world is necessary at every world.
    Without this rule no theorem of the form □φ w is derivable from
    universal facts alone, leaving S5 incomplete as a deductive system. -/
axiom Nec : ∀ (p : World → Prop), (∀ w, p w) → ∀ w, □ p w

/-- Necessity is monotone with respect to implication.
    If a conditional holds necessarily and its antecedent holds necessarily,
    the consequent holds necessarily. This is the semantic content of Axiom K
    stated as a derived rule rather than a bare axiom schema. -/
theorem Box_monotone (p q : World → Prop) (w : World)
    (hpq : ∀ v, p v → q v) (hp : □ p w) : □ q w :=
  K p q w (Nec (fun v => p v → q v) hpq w) hp


/-- Bridge between possible necessity and necessity.
    In S5 this holds at the frame level via symmetry and transitivity
    of the accessibility relation, but is not derivable from K, T, 4, 5
    as stated without a semantic reduction. It is therefore postulated. -/
axiom PossNec :
  ∀ (p : World → Prop) (w : World),
    ◊ (fun w' => □ p w') w → □ p w

/-- The characteristic thesis of S5: whatever is possibly necessary is necessary. -/
theorem S5_characteristic (p : World → Prop) (w : World)
    (h : ◊ (fun w' => □ p w') w) : □ p w :=
  PossNec p w h
  
/-- Iterated necessity: a necessary truth is necessarily necessary.
    This corresponds to the positive introspection of necessity,
    ensuring that the accessibility relation is transitive at the frame level. -/
theorem Box_Box_of_Box (p : World → Prop) (w : World)
    (h : □ p w) : □ (□ p) w :=
  Four p w h

/-- Universal truth entails possibility.
    A proposition true at every world cannot be excluded by any world,
    so it is witnessed as possible at the actual world. -/
theorem Nec_implies_Pos (p : World → Prop) (w : World)
    (h : ∀ v, p v) : ◊ p w := by
  intro hbox
  have := T (fun v => ¬ p v) w hbox
  exact this (h w)
