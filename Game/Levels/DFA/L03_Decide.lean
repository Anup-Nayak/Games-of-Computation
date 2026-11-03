import Game.Levels.DFA.L02_Accepts

World "DFA"
Level 3
Title "Let Lean check"

namespace Automata

Introduction "
For a fixed string, acceptance is a yes-or-no question that a computer can
answer by running the machine. The tactic `decide` does exactly that.

It only works on *concrete* questions: you cannot `decide` something about
every string.
"

/-- `parityA` accepts `abbab` but not `ba`. -/
Statement : [AB.a, .b, .b, .a, .b] ∈ parityA.accepts ∧ [AB.b, .a] ∉ parityA.accepts := by
  Hint "Both parts are about concrete strings. Use `decide`."
  decide

Conclusion "
`decide` checked both strings by running the machine. Note that `∉` is
*not in*: `w ∉ L` means `¬ (w ∈ L)`.
"

NewTactic decide

end Automata
