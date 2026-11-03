import Game.Levels.Subset.L04_Nil

World "Subset"
Level 5
Title "One symbol at a time"

namespace Automata

Introduction "
Second step. Reaching `r` from the *next* set `M.toDFA.step S x` by reading `xs`
is the same as reaching `r` from `S` by reading `x :: xs`: a first move from
some `p ∈ S`, then the rest of the path.
"

/-- `{r | ∃ q ∈ M.toDFA.step S x, M.Path q xs r} = {r | ∃ p ∈ S, M.Path p (x :: xs) r}` -/
TheoremDoc Automata.NFA.toDFA_onestep as "NFA.toDFA_onestep" in "Subset"
TheoremTab "Subset"

/-- Paths from the next set = paths from `S` that start with `x`. -/
Statement NFA.toDFA_onestep {α σ : Type} (M : NFA α σ) (S : Set σ) (x : α) (xs : List α) :
    {r | ∃ q ∈ M.toDFA.step S x, M.Path q xs r} = {r | ∃ p ∈ S, M.Path p (x :: xs) r} := by
  ext r
  constructor
  · intro h
    Hint "Take `{h}` apart: `obtain ⟨q, hq, hpath⟩ := {h}`."
    obtain ⟨q, hq, hpath⟩ := h
    Hint "`{hq}` says `{q}` is in the next set, so some `p ∈ {S}` moves to `{q}`.
    Take that apart too: `obtain ⟨p, hp, hpq⟩ := {hq}`."
    obtain ⟨p, hp, hpq⟩ := hq
    Hint "Start at `{p}`, move to `{q}`, then follow `{hpath}`:
    `exact ⟨{p}, {hp}, NFA.Path.cons {hpq} {hpath}⟩`."
    exact ⟨p, hp, NFA.Path.cons hpq hpath⟩
  · intro h
    obtain ⟨p, hp, hpath⟩ := h
    Hint "Split the path into its first move and the rest:
    `rw [NFA.path_cons_iff] at {hpath}`."
    rw [NFA.path_cons_iff] at hpath
    obtain ⟨q, hq, hpath'⟩ := hpath
    Hint "`{q}` is in the next set because `{p} ∈ {S}` moves to it. Nest the brackets:
    `exact ⟨{q}, ⟨{p}, {hp}, {hq}⟩, {hpath'}⟩`."
    exact ⟨q, ⟨p, hp, hq⟩, hpath'⟩

end Automata
