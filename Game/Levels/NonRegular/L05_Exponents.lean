import Game.Levels.NonRegular.L04_CountB

World "NonRegular"
Level 5
Title "Reading off the exponents"

namespace Automata

Introduction "
If `aⁱbʲ = aⁿbⁿ`, then `i = n = j`. Count the `a`s on both sides, then the `b`s.

`congrArg f h` turns an equation `h : x = y` into `f x = f y`: apply the same
function to both sides. For example, `congrArg (List.count AB.a) h`.
"

/-- `aⁱbʲ = aⁿbⁿ → i = j` -/
TheoremDoc Automata.replicate_eq as "replicate_eq" in "NonRegular"
TheoremTab "NonRegular"

/-- If `aⁱbʲ` is of the form `aⁿbⁿ`, then `i = j`. -/
Statement replicate_eq {i j n : ℕ}
    (h : List.replicate i AB.a ++ List.replicate j AB.b =
      List.replicate n AB.a ++ List.replicate n AB.b) : i = j := by
  Hint "Count the `a`s on both sides: `have ha := congrArg (List.count AB.a) {h}`."
  have ha := congrArg (List.count AB.a) h
  Hint "And the `b`s: `have hb := congrArg (List.count AB.b) {h}`."
  have hb := congrArg (List.count AB.b) h
  Hint "Simplify both with your counting results:
  `rw [count_a_ab, count_a_ab] at {ha}` and `rw [count_b_ab, count_b_ab] at {hb}`."
  rw [count_a_ab, count_a_ab] at ha
  rw [count_b_ab, count_b_ab] at hb
  Hint "`{ha} : {i} = {n}` and `{hb} : {j} = {n}`. `omega`."
  omega

NewTheorem congrArg

end Automata
