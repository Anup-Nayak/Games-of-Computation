import Game.Levels.NFA.L11_DFAPath

World "NFA"
Level 12
Title "Same language"

namespace Automata

Introduction "
**Final level of this world.** A DFA and its NFA version accept the same
language. So everything a DFA can do, an NFA can do too.

`DFA.toNFA_start : M.toNFA.start = M.start`
"

/-- `M.toNFA.accepts = M.accepts` -/
TheoremDoc Automata.DFA.toNFA_accepts as "DFA.toNFA_accepts" in "NFA"
TheoremTab "NFA"

/-- Viewing a DFA as an NFA doesn't change its language. -/
Statement DFA.toNFA_accepts {α σ : Type} (M : DFA α σ) : M.toNFA.accepts = M.accepts := by
  ext w
  Hint "Unfold both kinds of acceptance, and the start state:
  `rw [NFA.mem_accepts, DFA.mem_accepts, DFA.toNFA_start]`."
  rw [NFA.mem_accepts, DFA.mem_accepts, DFA.toNFA_start]
  constructor
  · intro h
    obtain ⟨f, hf, hp⟩ := h
    Hint "Turn the path `{hp}` into a run with `rw [DFA.toNFA_path] at {hp}`."
    rw [DFA.toNFA_path] at hp
    rw [hp]
    Hint "`{hf}` says `{f}` is accepting in `{M}.toNFA`, which has the same
    accepting states as `{M}`."
    exact hf
  · intro h
    Hint "The path ends where the run ends: `use {M}.evalFrom {M}.start {w}`."
    use M.evalFrom M.start w
    constructor
    · exact h
    · Hint "A path is a run: `rw [DFA.toNFA_path]`."
      rw [DFA.toNFA_path]

Conclusion "
**World complete.** NFAs can guess, and guessing made `containsAB` easy to
design. Every DFA is an NFA, so NFAs recognise *at least* the languages DFAs do.

Do they recognise more? That question is the subject of the Determinization world.
"

NewTheorem Automata.DFA.toNFA_start

end Automata
