import Game.Levels.DFA.L06_OnlyB

World "DFA"
Level 7
Title "Reading in two parts"

namespace Automata

Introduction "
Reading `u ++ v` is the same as reading `u`, then reading `v` from wherever you
ended up. This holds for *every* DFA `M`.

Induction on `u` is the natural plan. But be careful: when the machine reads
the first symbol `x`, its state changes from `q` to `M.step q x`. So the
induction hypothesis must work for *any* starting state, not just for `q`.

`induction' u with x xs ih generalizing q` makes the hypothesis hold for every
starting state.
"

/-- `M.evalFrom q (u ++ v) = M.evalFrom (M.evalFrom q u) v` -/
TheoremDoc Automata.DFA.evalFrom_append as "DFA.evalFrom_append" in "DFA"
TheoremTab "DFA"

/-- Reading `u ++ v` = reading `u`, then reading `v`. -/
Statement DFA.evalFrom_append {α σ : Type} (M : DFA α σ) (q : σ) (u v : List α) :
    M.evalFrom q (u ++ v) = M.evalFrom (M.evalFrom q u) v := by
  Hint "Induction on `{u}`, letting the starting state vary:
  `induction' {u} with x xs ih generalizing {q}`."
  Branch
    induction' u with x xs ih
    · rfl
    rw [List.cons_append]
    step
    step
    Hint "Stuck: `{ih}` is about starting in `{q}`, but the machine is now in
    `{M}.step {q} {x}`. Undo with **Retry**, and use
    `induction' u with x xs ih generalizing q` instead."
  induction' u with x xs ih generalizing q
  · Hint "`[] ++ v` is just `v`, and reading `[]` changes nothing. This is true by computation."
    rfl
  · Hint "`({x} :: {xs}) ++ {v}` doesn't show its first symbol yet. The theorem
    `List.cons_append` rewrites it to `{x} :: ({xs} ++ {v})`."
    rw [List.cons_append]
    Hint "Read the first symbol on both sides: `step` twice."
    step
    step
    Hint "`{ih}` works for any starting state. Use it with `{M}.step {q} {x}`:
    `exact {ih} ({M}.step {q} {x})`."
    exact ih (M.step q x)

Conclusion "
`generalizing` is needed whenever the thing you induct over changes another
variable along the way. For machines, it almost always does: the state changes
with every symbol.
"

NewTheorem List.cons_append

end Automata
