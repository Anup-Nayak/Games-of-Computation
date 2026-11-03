import Game.Levels.NonRegular.L02_Pigeonhole

World "NonRegular"
Level 3
Title "Counting a's"

namespace Automata

Introduction "
To tell the strings `aⁱbʲ` apart, count their letters. Three facts about `count`:

* `List.count_append : (l₁ ++ l₂).count a = l₁.count a + l₂.count a`
* `List.count_replicate_self : (List.replicate n a).count a = n`
* `List.count_replicate : (List.replicate n b).count a = if b == a then n else 0`

(`b == a` asks whether the symbols are equal; Lean can compute the answer.)
"

/-- `(List.replicate i AB.a ++ List.replicate j AB.b).count .a = i` -/
TheoremDoc Automata.count_a_ab as "count_a_ab" in "NonRegular"
TheoremTab "NonRegular"

/-- `aⁱbʲ` has `i` letters `a`. -/
Statement count_a_ab (i j : ℕ) : (List.replicate i AB.a ++ List.replicate j AB.b).count .a = i := by
  Hint "`rw [List.count_append, List.count_replicate_self, List.count_replicate]`"
  rw [List.count_append, List.count_replicate_self, List.count_replicate]
  Hint "`AB.b == AB.a` is false, so the `if` gives `0`, and `{i} + 0 = {i}`.
  All of this is computation: `rfl`."
  rfl

NewTheorem List.count_append List.count_replicate_self List.count_replicate

end Automata
