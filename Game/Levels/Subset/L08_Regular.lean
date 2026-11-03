import Game.Levels.Subset.L07_Accepts

World "Subset"
Level 8
Title "NFAs recognise regular languages"

namespace Automata

Introduction "
If `M` has finitely many states, then `M.toDFA` does too (`2ⁿ` of them).
`inferInstance` knows this. So every NFA language is regular, and NFAs recognise
**exactly** the regular languages, no more than DFAs.
"

/-- `[Finite σ] → M.accepts.IsRegular` -/
TheoremDoc Automata.NFA.accepts_isRegular as "NFA.accepts_isRegular" in "Subset"
TheoremTab "Subset"

/-- The language of a finite NFA is regular. -/
Statement NFA.accepts_isRegular {α σ : Type} [Finite σ] (M : NFA α σ) : M.accepts.IsRegular := by
  Hint "Give the subset machine: its states are `Set {σ}`.
  `exact ⟨Set {σ}, inferInstance, {M}.toDFA, NFA.toDFA_accepts {M}⟩`"
  exact ⟨Set σ, inferInstance, M.toDFA, NFA.toDFA_accepts M⟩

Conclusion "
Guessing doesn't add power, only convenience: an NFA can be exponentially smaller
than any DFA for the same language.
"

NewDefinition Set

end Automata
