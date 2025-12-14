import Basic.Truth
import Basic.Ontology

/--
Theorem 1 / 2:
Situations are extensionally identical if they make
the same propositions true.
-/
axiom Situation_extensionality :
  ∀ s s' : World,
    Situation s →
    Situation s' →
    (∀ p : Propn, s ⊨ p ↔ s' ⊨ p) →
    s = s'
