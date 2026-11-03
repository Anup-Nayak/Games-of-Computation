import Game.Levels.DFA
import Game.Levels.Closure

World "NonRegular"
Level 1
Title "A DFA forgets"

namespace Automata

Introduction "
A DFA's only memory is its current state. So if two strings `u` and `v` lead it
to the **same state**, it can never tell them apart afterwards: whatever comes
next, `u ++ w` and `v ++ w` get the same verdict.

This is the key to proving that some languages are **not** regular. You proved
`DFA.evalFrom_append` in the DFA world:
`M.evalFrom q (u ++ v) = M.evalFrom (M.evalFrom q u) v`.
"

/-- If `u` and `v` reach the same state, then `u ++ w ∈ M.accepts ↔ v ++ w ∈ M.accepts`. -/
TheoremDoc Automata.same_state_indist as "same_state_indist" in "NonRegular"
TheoremTab "NonRegular"

/-- Strings reaching the same state can't be told apart. -/
Statement same_state_indist {α σ : Type} (M : DFA α σ) {u v : List α}
    (h : M.evalFrom M.start u = M.evalFrom M.start v) (w : List α) :
    u ++ w ∈ M.accepts ↔ v ++ w ∈ M.accepts := by
  Hint "Unfold both acceptances, split both runs at the `++`, then use `{h}`:
  `rw [DFA.mem_accepts, DFA.mem_accepts, DFA.evalFrom_append, DFA.evalFrom_append, {h}]`."
  rw [DFA.mem_accepts, DFA.mem_accepts, DFA.evalFrom_append, DFA.evalFrom_append, h]

Conclusion "
After the last rewrite both sides were identical, so `rw` finished the proof by itself.
"

end Automata
