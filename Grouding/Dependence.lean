import Basic.Ontology
import Basic.Parthood

/-
  Ontological dependence between situations.

  A situation s depends on s' when s cannot obtain without s'.
  This formalizes the Fine–Correia tradition of grounding and
  dependence within the situation-theoretic framework, where
  dependence is defined not set-theoretically but through the
  encoding relation and modal operators.
-/

/-- s ontologically depends on s' when every possible situation
    that includes s also includes s'.
    Dependence is thus a necessary parthood condition: s cannot
    be part of any situation without s' also being part of it. -/
def OntologicallyDepends (s s' : World) : Prop :=
  ∀ u : World, Situation u → s ⊴ u → s' ⊴ u

notation s " ≺ " s' => OntologicallyDepends s s'

/-- A situation is trivially self-dependent.
    Everything requires itself in order to obtain. -/
theorem depends_refl (s : World) (hs : Situation s) : s ≺ s :=
  fun u _ hsu => hsu

/-- Dependence is transitive.
    If s requires s' and s' requires s'', then s requires s''. -/
theorem depends_trans (s s' s'' : World)
    (h  : s ≺ s')
    (h' : s' ≺ s'') : s ≺ s'' :=
  fun u hu hsu => h' u hu (h u hu hsu)

/-- Parthood implies dependence.
    If s is a part of s', then s depends on every situation
    that s' depends on — s inherits the dependence profile of
    its containing situation. -/
theorem part_implies_depends (s s' s'' : World)
    (hpart : s ⊴ s')
