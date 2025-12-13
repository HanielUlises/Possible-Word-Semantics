universe u

constant World : Type u

/-- Propositions are world-indexed -/
abbrev PropW := World → Prop

/-- Accessibility relation -/
constant Accessible : World → World → Prop

/-- Truth at a world -/
abbrev TrueIn (s : World) (p : PropW) : Prop :=
  p s

notation:50 s " ⊨ " p => TrueIn s p
