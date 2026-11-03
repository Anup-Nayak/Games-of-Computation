import Game.Levels.Subset.L02_Track

World "Subset"
Level 3
Title "What can't happen"

namespace Automata

Introduction "
`s2` is *not* in the set after reading just `a`: no single move gets from `s0`
to `s2`.

`Set.mem_singleton_iff : p ∈ {q} ↔ p = q`
"

/-- After reading `a` from `{s0}`, `s2` is not a possible state. -/
Statement : ABState.s2 ∉ containsAB.toDFA.evalFrom {.s0} [.a] := by
  step
  step
  Hint "`∉` is *not*: assume the opposite with `intro h`."
  intro h
  Hint "Take `{h}` apart: `obtain ⟨p, hp, hmove⟩ := {h}`."
  obtain ⟨p, hp, hmove⟩ := h
  Hint "`{hp}` says `{p}` is in `\{s0}`, so `{p} = s0`.
  `rw [Set.mem_singleton_iff] at {hp}`, then `rw [{hp}] at {hmove}`."
  rw [Set.mem_singleton_iff] at hp
  rw [hp] at hmove
  Hint "`{hmove}` claims the move `s0 → s2` on `a`, which isn't in the table. `cases {hmove}`."
  cases hmove

NewTheorem Set.mem_singleton_iff

end Automata
