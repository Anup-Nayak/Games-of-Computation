import Game.Levels.NFA.L05_PathCons

World "NFA"
Level 6
Title "A dead end"

namespace Automata

Introduction "
From `s1`, `containsAB` has no move on `a`. So no path reading `a` starts in `s1`,
whatever state you try to end in.

Use `NFA.path_cons_iff` on the assumption (`rw [...] at h`), then check every
state the first move could go to.
"

/-- No path reading `a` starts in `s1`. -/
Statement (r : ABState) : ¬ containsAB.Path .s1 [.a] r := by
  intro h
  Hint "Unfold the path in `{h}`: `rw [NFA.path_cons_iff] at {h}`."
  rw [NFA.path_cons_iff] at h
  Hint "Take it apart: `obtain ⟨q, hq, hp⟩ := {h}`."
  obtain ⟨q, hq, hp⟩ := h
  Hint "`{hq}` claims there is a move from `s1` to `{q}` on `a`. Check each state:
  `cases {q}`."
  cases q
  Hint "`{hq}` is a false concrete fact: the move table says `false = true`.
  `cases {hq}` sees that no proof of it can exist and closes the goal."
  cases hq
  cases hq
  cases hq

Conclusion "
`cases` on an impossible fact closes the goal: there is nothing left to prove.
"

end Automata
