import Game.Levels.Closure.L01_ComplRun

World "Closure"
Level 2
Title "The complement language"

namespace Automata

Introduction "
`M.compl` accepts exactly the strings `M` rejects.

`Lᶜ` is the complement of a language: `Set.mem_compl_iff : w ∈ Lᶜ ↔ w ∉ L`.
You'll also want `DFA.compl_start : M.compl.start = M.start`.
"

/-- `M.compl.accepts = M.acceptsᶜ` -/
TheoremDoc Automata.DFA.compl_accepts as "DFA.compl_accepts" in "Closure"
TheoremTab "Closure"

/-- The complement machine recognises the complement language. -/
Statement DFA.compl_accepts {α σ : Type} (M : DFA α σ) : M.compl.accepts = M.acceptsᶜ := by
  ext w
  Hint "Unfold everything: the complement, both acceptances, the start state,
  and the run.
  `rw [Set.mem_compl_iff, DFA.mem_accepts, DFA.mem_accepts, DFA.compl_start, DFA.compl_evalFrom]`"
  rw [Set.mem_compl_iff, DFA.mem_accepts, DFA.mem_accepts, DFA.compl_start, DFA.compl_evalFrom]
  Hint "Being in `{M}.compl.accept` means *not* being in `{M}.accept`, by definition.
  `rfl`."
  rfl

Conclusion "
The same run, the opposite verdict.
"

NewTheorem Set.mem_compl_iff Automata.DFA.compl_start

end Automata
