import Game.Levels.DFA.L01_Run

World "DFA"
Level 2
Title "Accepting a string"

namespace Automata

Introduction "
Every DFA has a **start state** and a set of **accepting states**. It accepts
a string if the run from the start state ends in an accepting state.

`parityA` starts in `even` and accepts in `even`.

The theorem `DFA.mem_accepts` unfolds acceptance:
`w ∈ M.accepts ↔ M.evalFrom M.start w ∈ M.accept`.
"

TheoremTab "DFA"

/-- `parityA` accepts `aa`. -/
Statement : [AB.a, .a] ∈ parityA.accepts := by
  Hint "Unfold what it means to accept with `rw [DFA.mem_accepts]`."
  rw [DFA.mem_accepts]
  Hint "Now run the machine with `step`."
  step
  step
  step
  Hint "The run ended in `even`. Is `even` an accepting state? The accepting set
  is `\{even}`, so this is true by computation."
  rfl

Conclusion "
The run was `even → odd → even`, and `even` is accepting.
"

NewTheorem Automata.DFA.mem_accepts
NewDefinition Automata.DFA.accepts

end Automata
