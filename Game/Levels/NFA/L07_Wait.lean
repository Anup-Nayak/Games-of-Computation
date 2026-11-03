import Game.Levels.NFA.L06_DeadEnd

World "NFA"
Level 7
Title "Waiting"

namespace Automata

Introduction "
From `s0`, `containsAB` can always stay in `s0`, whatever it reads. So it can
wait in `s0` through any string.
"

/-- `containsAB.Path .s0 u .s0` -/
TheoremDoc Automata.containsAB_wait as "containsAB_wait" in "NFA"
TheoremTab "NFA"

/-- `containsAB` can read any string and stay in `s0`. -/
Statement containsAB_wait (u : List AB) : containsAB.Path .s0 u .s0 := by
  Hint "Induction on `{u}`: `induction' {u} with x xs ih`."
  induction' u with x xs ih
  · Hint (hidden := true) "The empty string: the `nil` rule."
    exact NFA.Path.nil _
  · Hint "Stay in `s0` for the first symbol: `apply NFA.Path.cons (q := .s0)`."
    apply NFA.Path.cons (q := .s0)
    · Hint "The move `s0 → s0` is allowed on both symbols, but Lean needs to know
      which symbol `{x}` is before it can check. `cases {x}`, then `rfl` twice."
      cases x
      rfl
      rfl
    · exact ih

Conclusion "
Waiting in `s0` is what lets `containsAB` skip everything before the `ab`.
"

end Automata
