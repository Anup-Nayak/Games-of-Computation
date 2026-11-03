import Game.Levels.Strings.L03_Rewrite

World "Strings"
Level 4
Title "Union"

namespace Automata

Introduction "
Languages can be combined like sets. `L ∪ M` contains the strings in `L` *or* in `M`.
`L ⊆ M` means every string of `L` is also in `M`.

To prove `L ⊆ M`, take an arbitrary string `w` together with the fact `w ∈ L`,
and show `w ∈ M`. The tactic `intro w hw` does exactly this: it introduces
the string and the assumption.
"

/-- Every language is contained in its union with another language. -/
Statement (L M : Lang AB) : L ⊆ L ∪ M := by
  Hint "Start with `intro w hw`."
  intro w hw
  Hint "The goal is an *or*: `{w} ∈ {L}` or `{w} ∈ {M}`. Use `left` to say you
  will prove the left side, or `right` for the right side."
  left
  Hint "Now the goal is one of your assumptions."
  exact hw

Conclusion "
You now know how to prove a subset (`intro`) and an *or* (`left` or `right`).
"

NewTactic intro left right

end Automata
