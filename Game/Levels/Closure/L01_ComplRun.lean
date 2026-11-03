import Game.Metadata

World "Closure"
Level 1
Title "The complement machine"

namespace Automata

Introduction "
If a language is recognised by a DFA, is its **complement** too? Build the
machine: keep everything the same, but swap accepting and rejecting states.

```
def DFA.compl (M : DFA α σ) : DFA α σ :=
  { M with accept := M.acceptᶜ }
```

`{ M with accept := ... }` means: a copy of `M` with only `accept` changed.

First: since the moves didn't change, the runs didn't change either.
"

/-- `M.compl.evalFrom q w = M.evalFrom q w` -/
TheoremDoc Automata.DFA.compl_evalFrom as "DFA.compl_evalFrom" in "Closure"
TheoremTab "Closure"

/-- The complement machine runs exactly like the original. -/
Statement DFA.compl_evalFrom {α σ : Type} (M : DFA α σ) (q : σ) (w : List α) :
    M.compl.evalFrom q w = M.evalFrom q w := by
  Hint "Induction on `{w}`, generalizing `{q}`."
  induction' w with x xs ih generalizing q
  · rfl
  · Hint "Read the first symbol on both sides. `step` knows that `{M}.compl`
    moves like `{M}`."
    step
    step
    Hint (hidden := true) "`exact {ih} ({M}.step {q} {x})`"
    exact ih (M.step q x)

NewDefinition Automata.DFA.compl

end Automata
