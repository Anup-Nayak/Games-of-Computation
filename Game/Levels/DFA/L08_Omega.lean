import Game.Levels.DFA.L07_Append

World "DFA"
Level 8
Title "Even and odd numbers"

namespace Automata

Introduction "
`parityA` counts `a`s modulo 2. To reason about it we need small facts about
remainders, such as: if `n` is even then `n + 1` is not.

`omega` proves goals built from `+`, `-`, numbers, `%` by a constant,
comparisons and `=`/`≠` over the natural numbers, using your assumptions.
"

/-- If `n` is even, then `n + 1` is odd. -/
Statement (n : ℕ) (h : n % 2 = 0) : (n + 1) % 2 ≠ 0 := by
  Hint "This is a job for `omega`."
  omega

Conclusion "
`omega` saves you from arithmetic you would otherwise do by hand.
"

NewTactic omega

end Automata
