import Basic.Ontology

/-
  KRIPKE FRAMES

  A Kripke frame consists of a set of worlds together
  with an accessibility relation.

  No modal principles are assumed at this level.
-/

/--
  Accessibility relation between worlds.
-/
axiom R : World → World → Prop

/--
  Reflexivity of accessibility.

  Every world accesses itself.
-/
axiom R_refl : ∀ w : World, R w w

/--
  Transitivity of accessibility.

  Accessibility is closed under chaining.
-/
axiom R_trans : ∀ w u v : World, R w u → R u v → R w v

/--
  Symmetry of accessibility.

  Accessibility is bidirectional.
-/
axiom R_symm : ∀ w u : World, R w u → R u w
