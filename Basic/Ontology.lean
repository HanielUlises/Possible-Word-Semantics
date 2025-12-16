universe u

/-
  ontological primitives.

  this file introduces the basic entities of the theory.
  all notions are taken as primitive and governed by axioms,
  in the spirit of higher-order modal and situation semantics.
-/

/--
  the domain of objects.

  worlds and situations are not distinguished at the type level.
-/
axiom World : Type u

/--
  the domain of properties.

  properties are intensional entities which may be encoded.
-/
axiom Property : Type u

/--
  the domain of propositions.

  propositions are intensional and evaluated relative to situations.
-/
axiom Propn : Type u

/--
  objecthood predicate.

  this allows us to state axioms that apply only to objects.
-/
axiom Object : World → Prop

/--
  situationhood predicate.

  situations are partial objects.
-/
axiom Situation : World → Prop

/--
  encoding relation between objects and properties.

  `Enc x F` means that x encodes property F.
-/
axiom Enc : World → Property → Prop

/--
  encoding relation between objects and propositions.

  this is treated as primitive to match the prover9 theory.
-/
axiom Encp : World → Propn → Prop

/--
  vacuous abstraction operator.

  maps propositions to corresponding properties.
-/
axiom VAC : Propn → Property
