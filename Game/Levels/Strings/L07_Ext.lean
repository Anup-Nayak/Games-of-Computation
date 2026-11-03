import Game.Levels.Strings.L06_Obtain

World "Strings"
Level 7
Title "Equal languages"

namespace Automata

Introduction "
Two languages are equal when they contain the same strings. The tactic `ext w`
turns the goal `L = M` into `w ∈ L ↔ w ∈ M` for an arbitrary string `w`.

An *iff* `A ↔ B` is two implications, so `constructor` splits it into
`A → B` and `B → A`.

Finally, an *or* in an assumption is taken apart into two cases with
`obtain h | h := h`: one case where the left side holds, one where the right side holds.
"

/-- `L ∪ M = M ∪ L` -/
TheoremDoc Automata.Lang.union_comm as "Lang.union_comm" in "Languages"
TheoremTab "Languages"

/-- `L ∪ M` and `M ∪ L` are the same language. -/
Statement Lang.union_comm (L M : Lang AB) : L ∪ M = M ∪ L := by
  Hint "Start with `ext w`."
  ext w
  Hint "Split the *iff* with `constructor`."
  constructor
  · Hint (hidden := true) "Introduce the assumption with `intro h`."
    intro h
    Hint "`{h}` is an *or*. Split into two cases with `obtain h | h := {h}`."
    obtain h | h := h
    · Hint (hidden := true) "In this case `{w}` is in the left language, which is
      on the right of the goal."
      right
      exact h
    · left
      exact h
  · intro h
    obtain h | h := h
    · right
      exact h
    · left
      exact h

Conclusion "
This is the pattern for every equality of languages in the game: `ext`, then
prove both directions.

You proved a named result, `Lang.union_comm`. It is now in your inventory under
*Theorems*, and you can use it in later levels.
"

NewTactic ext

end Automata
