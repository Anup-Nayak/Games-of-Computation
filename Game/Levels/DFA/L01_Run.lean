import Game.Metadata

World "DFA"
Level 1
Title "Running a machine"

open Automata

Introduction "
A deterministic finite automaton reads a string one symbol at a time,
moving from state to state.

Our first machine, `parityA`, has two states: `even` and `odd`.
Reading `a` swaps them; reading `b` changes nothing.
"

/-- Starting in `even`, after reading `ab` the machine is in `odd`. -/
Statement : parityA.evalFrom .even [.a, .b] = .odd := by
  Hint "Both sides compute to the same state: `a` takes `even` to `odd`,
  then `b` leaves it there. When two sides are equal just by computing,
  `rfl` proves it."
  rfl

Conclusion "
Lean ran the machine for you. Soon you'll prove things about runs of
*every* length, where computing is no longer enough.
"

NewTactic rfl
NewDefinition Automata.DFA.evalFrom Automata.parityA
