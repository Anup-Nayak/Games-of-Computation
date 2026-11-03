import Game.Levels.DFA.L03_Decide

World "DFA"
Level 4
Title "A counterexample"

namespace Automata

Introduction "
Someone claims that `parityA` accepts *every* string. Show that they are wrong.

`¬ P` means *P leads to a contradiction*: to prove it, assume `P` with
`intro h` and derive `False`.

The tactic `have` adds a new fact to your assumptions:
`have h₁ := h [AB.a]` applies `h` to the string `a`, and
`have h₂ : P := by ...` proves `P` on the spot.
"

/-- `parityA` does not accept every string. -/
Statement : ¬ ∀ w : List AB, w ∈ parityA.accepts := by
  Hint "Assume the claim: `intro h`."
  intro h
  Hint "Find a string that `parityA` rejects, and apply `{h}` to it,
  for example `have h₁ := {h} [AB.a]`."
  have h₁ := h [AB.a]
  Hint "Now prove that the string is *not* accepted. It is a concrete
  question: `have h₂ : [AB.a] ∉ parityA.accepts := by decide`."
  have h₂ : [AB.a] ∉ parityA.accepts := by decide
  Hint "`{h₂}` says *not* `{h₁}`, that is, `{h₁}` leads to `False`. A proof of
  `¬ P` works like a function: `exact {h₂} {h₁}`."
  exact h₂ h₁

Conclusion "
To refute a claim about all strings, one counterexample is enough.
"



end Automata
