import Game.Levels.NFA.L01_Path

World "NFA"
Level 2
Title "Choosing the moves"

namespace Automata

Introduction "
Here are the moves of `containsAB`:

| from | reading | may go to |
|---|---|---|
| `s0` | `a` | `s0` or `s1` |
| `s0` | `b` | `s0` |
| `s1` | `b` | `s2` |
| `s2` | `a` or `b` | `s2` |

From `s1` reading `a` there is **no** move. `s0` waits; on an `a` it may *guess*
that this is the start of `ab` and jump to `s1`.

To build a path one move at a time, use `apply NFA.Path.cons (q := s)` where `s`
is the state you choose to move to. Lean then asks for two things: that the move
is allowed, and the rest of the path. Whether a move is allowed is a concrete
fact, so `rfl` proves it.
"

/-- `[a, b] : s0 → s2` -/
TheoremDoc Automata.containsAB_ab as "containsAB_ab" in "NFA"
TheoremTab "NFA"

/-- Reading `ab`, `containsAB` can get from `s0` to `s2`. -/
Statement containsAB_ab : containsAB.Path .s0 [.a, .b] .s2 := by
  Hint "Reading `a` from `s0`, guess that the `ab` starts here and move to `s1`:
  `apply NFA.Path.cons (q := .s1)`."
  apply NFA.Path.cons (q := .s1)
  · Hint "Is `s0 → s1` on `a` an allowed move? Check by computation: `rfl`."
    rfl
  Hint "Now read `b`. From `s1`, where can you go?"
  apply NFA.Path.cons (q := .s2)
  · rfl
  Hint "Nothing left to read."
  exact NFA.Path.nil _

Conclusion "
`apply` works backwards: it fits the goal to the end of a rule and leaves you the
rule's assumptions as new goals.
"

NewTactic apply

end Automata
