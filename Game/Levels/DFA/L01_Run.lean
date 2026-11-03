import Game.Metadata

World "DFA"
Level 1
Title "Running a machine"

namespace Automata

Introduction "
A **deterministic finite automaton** (DFA) has finitely many states. It reads a
string one symbol at a time, and each symbol moves it to a new state.

Our first machine, `parityA`, has two states: `even` and `odd`.
Reading `a` swaps them; reading `b` changes nothing.

`parityA.evalFrom q w` is the state the machine ends in after reading `w`,
starting from state `q`.

The tactic `step` makes the machine read one symbol, so you can watch the run.
"

/-- Starting in `even`, after reading `ab` the machine is in `odd`. -/
Statement : parityA.evalFrom .even [.a, .b] = .odd := by
  Hint "Use `step` to read the first symbol."
  step
  Hint "The machine read `a` and moved from `even` to `odd`. One symbol is
  left: `step` again."
  step
  Hint "Nothing is left to read. One last `step` finishes the run."
  step

Conclusion "
You watched the run `even → odd → odd`.

(`rfl` would also have worked here: Lean can compute the whole run at once.
`step` lets you see each state along the way.)

Running a machine on a *concrete* string is computation. Soon you will prove
things about runs on *every* string, where computing is no longer enough.
"

NewTactic step
NewDefinition Automata.DFA Automata.DFA.evalFrom Automata.parityA Automata.Parity

end Automata
