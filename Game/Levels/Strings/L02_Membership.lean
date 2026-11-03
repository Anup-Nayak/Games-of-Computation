import Game.Levels.Strings.L01_Append

World "Strings"
Level 2
Title "Languages are sets"

namespace Automata

Introduction "
A **language** is a set of strings. `Lang AB` is the type of languages over our
alphabet.

The most common way to describe a language is by a property. For example
`{u | u.length = 2}` is the language of strings of length 2. A string `w` is
in that language exactly when `w.length = 2`: membership *is* the property.
"

/-- If `w` has length 2, then `w` is in the language of strings of length 2. -/
Statement (w : List AB) (h : w.length = 2) : w ∈ ({u | u.length = 2} : Lang AB) := by
  Hint "Look at the assumption `{h}`. It says exactly what the goal asks for,
  because being in `\{u | u.length = 2}` just means having length 2.
  Use `exact {h}`."
  exact h

Conclusion "
`exact h` closes a goal with a proof `h` you already have. Lean accepted `h` even
though the goal was written as a membership: it unfolded the definition and saw
the same statement underneath.
"

NewTactic exact
NewDefinition Automata.Lang

end Automata
