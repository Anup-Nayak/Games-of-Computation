import Game.Levels.NFA.L10_ContainsAB

World "NFA"
Level 11
Title "Every DFA is an NFA"

namespace Automata

Introduction "
A DFA is an NFA that always has exactly one move. `M.toNFA` is the DFA `M` viewed
as an NFA, with `M.toNFA.step p x = {M.step p x}`, a set with one state.

`DFA.mem_toNFA_step : q ∈ M.toNFA.step p x ↔ q = M.step p x`

You'll also need the rule that `step` has been using all along:
`DFA.evalFrom_cons : M.evalFrom q (x :: xs) = M.evalFrom (M.step q x) xs`.

For `M.toNFA`, a path is the same as a run: the path from `p` reading `w`
reaches `r` exactly when the run does.
"

/-- `M.toNFA.Path p w r ↔ M.evalFrom p w = r` -/
TheoremDoc Automata.DFA.toNFA_path as "DFA.toNFA_path" in "NFA"
TheoremTab "NFA"

/-- For a DFA viewed as an NFA, paths are runs. -/
Statement DFA.toNFA_path {α σ : Type} (M : DFA α σ) (p r : σ) (w : List α) :
    M.toNFA.Path p w r ↔ M.evalFrom p w = r := by
  Hint "Induction on `{w}`, generalizing `{p}`."
  induction' w with x xs ih generalizing p
  · Hint "Unfold the path: `rw [NFA.path_nil_iff]`. Both sides then say the same
    thing, by computation."
    rw [NFA.path_nil_iff]
    rfl
  · Hint "Unfold both sides one symbol: `rw [NFA.path_cons_iff, DFA.evalFrom_cons]`.
    Then turn the run on the right back into a path using the induction
    hypothesis backwards: `rw [← {ih} ({M}.step {p} {x})]`."
    rw [NFA.path_cons_iff, DFA.evalFrom_cons, ← ih (M.step p x)]
    constructor
    · intro h
      obtain ⟨q, hq, hp⟩ := h
      Hint "`{hq}` says `{q}` is the only possible next state:
      `rw [DFA.mem_toNFA_step] at {hq}`."
      rw [DFA.mem_toNFA_step] at hq
      Hint (hidden := true) "Now `rw [{hq}] at {hp}` and you're done."
      rw [hq] at hp
      exact hp
    · intro h
      Hint "Give the one possible next state. The move is allowed by `rfl`:
      `exact ⟨{M}.step {p} {x}, rfl, {h}⟩`."
      exact ⟨M.step p x, rfl, h⟩

Conclusion "
`rw [← h]` rewrites right-to-left: it replaced the run by the path.
"

NewDefinition Automata.DFA.toNFA
NewTheorem Automata.DFA.mem_toNFA_step Automata.DFA.evalFrom_cons

end Automata
