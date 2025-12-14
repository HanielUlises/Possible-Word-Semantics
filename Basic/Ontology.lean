universe u v

/-
  ontology

  primitive entities of the framework.
  all structure is imposed axiomatically.
-/

/--
  worlds or situations
-/
axiom World : Type u

/--
  properties as higher-order entities

  declared as a Sort rather than a Type to allow
  unrestricted quantification in propositions.
-/
axiom Property : Sort v

/--
  encoding relation
-/
axiom Enc : World → Property → Prop

/--
  situationhood predicate
-/
axiom Situation : World → Prop
