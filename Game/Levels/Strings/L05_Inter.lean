import Game.Levels.Strings.L04_Subset

World "Strings"
Level 5
Title "Intersection"

namespace Automata

Introduction "
`L ∩ M` contains the strings that are in `L` *and* in `M`. To prove an *and*,
prove both parts. The tactic `constructor` splits the goal into its two parts.
"

/-- A string in both `L` and `M` is in `L ∩ M`. -/
Statement (L M : Lang AB) (w : List AB) (h₁ : w ∈ L) (h₂ : w ∈ M) : w ∈ L ∩ M := by
  Hint "Use `constructor` to split the goal into two."
  constructor
  Hint "First part: `{w} ∈ {L}`."
  exact h₁
  Hint "Second part."
  exact h₂

Conclusion "
When there are several goals, Lean works on the first one, and you can see the
others below it.
"

NewTactic constructor

end Automata
