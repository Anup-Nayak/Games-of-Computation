import Game.Levels.Strings.L05_Inter

World "Strings"
Level 6
Title "Taking apart an *and*"

namespace Automata

Introduction "
`constructor` builds an *and*. To *use* an *and* that you have as an assumption,
take it apart: `obtain ⟨h₁, h₂⟩ := h` replaces `h : A ∧ B` by `h₁ : A` and `h₂ : B`.

(Type `⟨` as `\\<` and `⟩` as `\\>`.)
"

/-- Intersection does not depend on the order. -/
Statement (L M : Lang AB) : L ∩ M ⊆ M ∩ L := by
  Hint (hidden := true) "Start the same way as for a subset: `intro w hw`."
  intro w hw
  Hint "`{hw}` says `{w}` is in both languages. Take it apart with
  `obtain ⟨h₁, h₂⟩ := {hw}`."
  obtain ⟨h₁, h₂⟩ := hw
  Hint (hidden := true) "Now build the *and* in the goal, in the other order."
  constructor
  exact h₂
  exact h₁

Conclusion "
`obtain` takes things apart; `constructor` puts them together.
"

NewTactic obtain

end Automata
