import Game.Levels.NFA.L07_Wait

World "NFA"
Level 8
Title "Staying"

namespace Automata

Introduction "
Once in `s2`, `containsAB` stays there whatever it reads. Same idea as the
last level.
"

/-- `containsAB.Path .s2 v .s2` -/
TheoremDoc Automata.containsAB_stay as "containsAB_stay" in "NFA"
TheoremTab "NFA"

/-- `containsAB` can read any string and stay in `s2`. -/
Statement containsAB_stay (v : List AB) : containsAB.Path .s2 v .s2 := by
  Hint (hidden := true) "Same plan as last level: `induction' {v} with x xs ih`."
  induction' v with x xs ih
  · exact NFA.Path.nil _
  · apply NFA.Path.cons (q := .s2)
    · cases x
      rfl
      rfl
    · exact ih

end Automata
