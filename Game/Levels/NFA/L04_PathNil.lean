import Game.Levels.NFA.L03_Accepts

World "NFA"
Level 4
Title "Taking a path apart: nothing read"

namespace Automata

Introduction "
So far you have *built* paths. To *use* a path you have as an assumption, take
it apart. Since `NFA.Path.nil` and `NFA.Path.cons` are the only ways to build
a path, any path must come from one of them.

`cases h` does this for an assumption `h : M.Path p w r`. It looks at which
rules could have produced `h`. For a path reading `[]`, only `nil` fits, and
`nil` forces the two ends to be equal.

This holds for *every* NFA. In the next levels you'll prove a few general facts
like this one and use them for the rest of the game.
"

/-- `M.Path p [] r ↔ p = r` -/
TheoremDoc Automata.NFA.path_nil_iff as "NFA.path_nil_iff" in "NFA"
TheoremTab "NFA"

/-- A path reading nothing starts and ends in the same state. -/
Statement NFA.path_nil_iff {α σ : Type} (M : NFA α σ) (p r : σ) :
    M.Path p [] r ↔ p = r := by
  Hint "Two directions: `constructor`."
  constructor
  · intro h
    Hint "Take the path `{h}` apart with `cases {h}`. Only `nil` reads `[]`,
    and it forces `{p}` and `{r}` to be the same state."
    cases h
    rfl
  · intro h
    Hint "Rewrite with `{h}`, then use the `nil` rule."
    rw [h]
    exact NFA.Path.nil r

Conclusion "
`cases` worked out that `p` and `r` had to be the same and replaced one by
the other.
"

end Automata
