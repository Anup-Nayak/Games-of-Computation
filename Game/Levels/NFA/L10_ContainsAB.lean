import Game.Levels.NFA.L09_Glue

World "NFA"
Level 10
Title "Finding the ab"

namespace Automata

Introduction "
**Boss level.** `containsAB` accepts every string that contains `ab`.

A path for `u ++ [a, b] ++ v`: wait in `s0` through `u`, read `ab` from `s0` to
`s2`, then stay in `s2` through `v`. You have proved each piece:
`containsAB_wait`, `containsAB_ab`, `containsAB_stay`. Glue them with
`NFA.path_append`.

(`u ++ [a, b] ++ v` means `(u ++ [a, b]) ++ v`.)
"

TheoremTab "NFA"

/-- `containsAB` accepts every string with `ab` in it. -/
Statement (u v : List AB) : u ++ [.a, .b] ++ v ∈ containsAB.accepts := by
  rw [NFA.mem_accepts]
  Hint (hidden := true) "End in `s2`: `use .s2`, then `constructor`."
  use .s2
  constructor
  · rfl
  · Hint "First glue the waiting and the `ab`:
    `have h₁ := NFA.path_append (containsAB_wait {u}) containsAB_ab`."
    have h₁ := NFA.path_append (containsAB_wait u) containsAB_ab
    Hint "`{h₁}` gets you to `s2` after `{u} ++ [a, b]`. Glue the rest."
    exact NFA.path_append h₁ (containsAB_stay v)

Conclusion "
The NFA guessed *where* the `ab` starts. A DFA for this language exists too,
but it has to keep track of more. You'll see in a later world that every NFA can
be turned into a DFA.
"

end Automata
