import Game.Levels.Strings.L02_Membership

World "Strings"
Level 3
Title "Rewriting"

namespace Automata

Introduction "
When you know `u = [.a]`, you can replace `u` by `[.a]` anywhere in the goal.
The tactic `rw [h]` does this: it rewrites the left side of `h` into the right side.
"

/-- If `u` is the string `a`, then `u ++ v` is `a` followed by `v`. -/
Statement (u v : List AB) (h : u = [.a]) : u ++ v = .a :: v := by
  Hint "Use `rw [{h}]` to replace `{u}` by `[AB.a]`."
  rw [h]
  Hint "Both sides now compute to the same list: `[a] ++ v` is `a` in front of `v`."
  rfl

Conclusion "
Here `a :: v` means the string that starts with `a` and continues with `v`.
Every non-empty string has this shape, which is how machines will read strings:
one symbol at a time from the front.
"

NewTactic rw

end Automata
