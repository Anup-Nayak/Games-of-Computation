import Game.Metadata

World "Strings"
Level 1
Title "Strings are lists"

namespace Automata

Introduction "
Every machine in this game reads **strings**. A string is a list of symbols.
Our alphabet `AB` has two symbols, `AB.a` and `AB.b`, and Lean writes a string
like `aba` as the list `[AB.a, AB.b, AB.a]`. When the type is clear, you may
shorten a symbol to `.a`.

Gluing two strings together is written `++`.
"

/-- Gluing `ab` and `a` gives `aba`. -/
Statement : [AB.a, .b] ++ [.a] = [.a, .b, .a] := by
  Hint "Lean can glue these two concrete strings itself and see that both sides
  are the same list. The tactic `rfl` proves a goal `X = Y` when `X` and `Y`
  compute to the same thing."
  rfl

Conclusion "
`rfl` (short for *reflexivity*) is the simplest proof there is: both sides are
literally equal once Lean computes them.
"

NewTactic rfl
NewDefinition Automata.AB Automata.AB.a Automata.AB.b

end Automata
