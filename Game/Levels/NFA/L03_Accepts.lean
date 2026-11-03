import Game.Levels.NFA.L02_Moves

World "NFA"
Level 3
Title "Accepting by guessing right"

namespace Automata

Introduction "
An NFA **accepts** a string if *some* path from the start state ends in an
accepting state:

`NFA.mem_accepts : w ∈ M.accepts ↔ ∃ f ∈ M.accept, M.Path M.start w f`

`containsAB` accepts only in `s2`.

To prove an `∃`, the tactic `use` lets you name the witness. After `use s`, you
still have to show that `s` works.
"

TheoremTab "NFA"

/-- `containsAB` accepts `bab`. -/
Statement : [AB.b, .a, .b] ∈ containsAB.accepts := by
  Hint "Unfold acceptance: `rw [NFA.mem_accepts]`."
  rw [NFA.mem_accepts]
  Hint "Which state should the path end in? Only `s2` is accepting: `use .s2`."
  use .s2
  Hint "Two things to show: `s2` is accepting, and there is a path. `constructor`."
  constructor
  · rfl
  Hint "The first symbol is `b`, so the `ab` doesn't start here. Stay in `s0`."
  Branch
    apply NFA.Path.cons (q := .s1)
    Hint "There is no move from `s0` to `s1` on `b`, so this goal is false.
    Undo with **Retry** and choose another state."
  apply NFA.Path.cons (q := .s0)
  · rfl
  Hint "Now `a`: this time the `ab` *does* start here. Guess it."
  apply NFA.Path.cons (q := .s1)
  · rfl
  apply NFA.Path.cons (q := .s2)
  · rfl
  exact NFA.Path.nil _

Conclusion "
A wrong guess doesn't make the machine reject the string. It just means that
path fails. The string is accepted as soon as *one* path works.
"

NewTactic use
NewTheorem Automata.NFA.mem_accepts

end Automata
