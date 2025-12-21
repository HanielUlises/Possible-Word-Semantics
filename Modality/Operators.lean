import Basic.Ontology

/-
  KRIPKEAN MODALITY

  Modality is interpreted using standard Kripke semantics.
  Worlds (including situations) are related by an accessibility
  relation representing modal possibility.

  No structural properties of accessibility (e.g. reflexivity,
  transitivity, symmetry) are assumed at this stage.
-/

/--
  Accessibility relation between worlds.

  `Accessible w₁ w₂` means that world `w₂` is modally accessible
  from world `w₁`.
-/
axiom Accessible : World → World → Prop

/--
  Possibility operator.

  `◊ φ` holds iff there exists an accessible world in which φ holds.
-/
def Diamond (φ : World → Prop) (w : World) : Prop :=
  ∃ w' : World, Accessible w w' ∧ φ w'

/--
  Necessity operator.

  `□ φ` holds iff φ holds in all accessible worlds.
-/
def Box (φ : World → Prop) (w : World) : Prop :=
  ∀ w' : World, Accessible w w' → φ w'

notation "◊" => Diamond
notation "□" => Box
