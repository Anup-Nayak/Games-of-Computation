import Game.Levels.Subset.L06_Run

World "Subset"
Level 7
Title "Same language"

namespace Automata

Introduction "
The subset machine accepts exactly the strings the NFA accepts.

`NFA.toDFA_start : M.toDFA.start = {M.start}`. A set is accepting when it
contains an accepting state, so membership in `M.toDFA.accept` can be taken apart
with `obtain` like any `∃`.
"

/-- `M.toDFA.accepts = M.accepts` -/
TheoremDoc Automata.NFA.toDFA_accepts as "NFA.toDFA_accepts" in "Subset"
TheoremTab "Subset"

/-- The subset construction is correct. -/
Statement NFA.toDFA_accepts {α σ : Type} (M : NFA α σ) : M.toDFA.accepts = M.accepts := by
  ext w
  Hint "Unfold both acceptances, the start set, and the run:
  `rw [DFA.mem_accepts, NFA.mem_accepts, NFA.toDFA_start, NFA.toDFA_evalFrom]`."
  rw [DFA.mem_accepts, NFA.mem_accepts, NFA.toDFA_start, NFA.toDFA_evalFrom]
  constructor
  · intro h
    Hint "The final set contains an accepting state:
    `obtain ⟨f, hf, hacc⟩ := {h}`."
    obtain ⟨f, hf, hacc⟩ := h
    Hint "`{f}` is reachable from `\{M.start}`: take `{hf}` apart too."
    obtain ⟨p, hp, hpath⟩ := hf
    Hint (hidden := true) "`rw [Set.mem_singleton_iff] at {hp}`, `rw [{hp}] at {hpath}`."
    rw [Set.mem_singleton_iff] at hp
    rw [hp] at hpath
    exact ⟨f, hacc, hpath⟩
  · intro h
    obtain ⟨f, hf, hpath⟩ := h
    Hint "`{f}` is in the final set, reached from `{M}.start`, and it's accepting.
    `exact ⟨{f}, ⟨{M}.start, rfl, {hpath}⟩, {hf}⟩`"
    exact ⟨f, ⟨M.start, rfl, hpath⟩, hf⟩

NewTheorem Automata.NFA.toDFA_start

end Automata
