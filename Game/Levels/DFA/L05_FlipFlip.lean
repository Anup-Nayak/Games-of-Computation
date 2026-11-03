import Game.Levels.DFA.L04_Counterexample

World "DFA"
Level 5
Title "Two flips"

namespace Automata

Introduction "
`Parity.flip` swaps the two states. Flipping twice should change nothing,
for *every* state `q`.

There are only two states, so check them one by one: `cases q` splits the
goal into one case for `even` and one for `odd`.
"

/-- `q.flip.flip = q` -/
TheoremDoc Automata.Parity.flip_flip as "Parity.flip_flip" in "DFA"
TheoremTab "DFA"

/-- Flipping twice gives back the state you started from. -/
Statement Parity.flip_flip (q : Parity) : q.flip.flip = q := by
  Hint "Split on the state with `cases q`."
  cases q
  Hint "Each case is now a concrete computation."
  rfl
  rfl

Conclusion "
`cases` works on anything with finitely many shapes: states, symbols, *or*s.
"

NewTactic cases
NewDefinition Automata.Parity.flip

end Automata
