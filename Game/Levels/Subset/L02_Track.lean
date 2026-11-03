import Game.Levels.Subset.L01_SubsetStep

World "Subset"
Level 2
Title "Running the subset machine"

namespace Automata

Introduction "
Run `containsAB.toDFA` from `{s0}` on the string `a`. `containsAB` could have
stayed in `s0` or guessed `s1`, so both should be in the resulting set.

`step` works on the subset machine too: it shows the next set as
`{r | ∃ p ∈ S, r ∈ containsAB.step p x}`.
"

/-- After reading `a` from `{s0}`, `s1` is among the possible states. -/
Statement : ABState.s1 ∈ containsAB.toDFA.evalFrom {.s0} [.a] := by
  Hint "Read the `a` with `step`, then finish the run with another `step`."
  step
  step
  Hint "The goal asks for a state `p ∈ \{s0}` with a move `p → s1` on `a`. Take
  `p = s0`: being in `\{s0}` and the move are both true by `rfl`.
  `exact ⟨.s0, rfl, rfl⟩`"
  exact ⟨.s0, rfl, rfl⟩

Conclusion "
In the same way, `s0` is in this set too. The set is exactly `{s0, s1}`: every
place the guesses could lead.
"

end Automata
