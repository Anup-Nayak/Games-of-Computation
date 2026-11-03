import Game.Levels.NonRegular.L03_CountA

World "NonRegular"
Level 4
Title "Counting b's"

namespace Automata

Introduction "
The same for `b`. This time the `0` comes *first*, as in `0 + j`, and Lean can't
simplify that by computation alone when `j` is a variable. Remove the `if` with
`if_neg`, and let `omega` finish.
"

/-- `(List.replicate i AB.a ++ List.replicate j AB.b).count .b = j` -/
TheoremDoc Automata.count_b_ab as "count_b_ab" in "NonRegular"
TheoremTab "NonRegular"

/-- `aⁱbʲ` has `j` letters `b`. -/
Statement count_b_ab (i j : ℕ) : (List.replicate i AB.a ++ List.replicate j AB.b).count .b = j := by
  rw [List.count_append, List.count_replicate_self, List.count_replicate]
  Hint "`AB.a == AB.b` is false, and `decide` can show it:
  `rw [if_neg (by decide)]`."
  rw [if_neg (by decide)]
  Hint (hidden := true) "`omega`"
  omega

end Automata
