import Game.Levels.Subset.L03_NotS2

World "Subset"
Level 4
Title "What the set means"

namespace Automata

Introduction "
The key claim: after reading `w` from a set `S`, the subset machine is in the set
of **all states reachable from `S` by a path reading `w`**.

`M.toDFA.evalFrom S w = {r | ∃ p ∈ S, M.Path p w r}`

You'll prove it in three steps. First, the empty string: reading nothing, the
machine stays in `S`, and the states reachable from `S` by reading nothing are
exactly those of `S`.
"

/-- `M.toDFA.evalFrom S [] = {r | ∃ p ∈ S, M.Path p [] r}` -/
TheoremDoc Automata.NFA.toDFA_evalFrom_nil as "NFA.toDFA_evalFrom_nil" in "Subset"
TheoremTab "Subset"

/-- Reading nothing, the subset machine's set is what's reachable by reading nothing. -/
Statement NFA.toDFA_evalFrom_nil {α σ : Type} (M : NFA α σ) (S : Set σ) :
    M.toDFA.evalFrom S [] = {r | ∃ p ∈ S, M.Path p [] r} := by
  Hint "Two sets are equal when they have the same elements: `ext r`."
  ext r
  constructor
  · intro h
    Hint "`{r}` itself is in `{S}`, and the empty path goes from `{r}` to `{r}`.
    `exact ⟨{r}, {h}, NFA.Path.nil {r}⟩`"
    exact ⟨r, h, NFA.Path.nil r⟩
  · intro h
    obtain ⟨p, hp, hpath⟩ := h
    Hint "A path reading nothing doesn't move: `rw [NFA.path_nil_iff] at {hpath}`."
    rw [NFA.path_nil_iff] at hpath
    Hint (hidden := true) "`rw [← {hpath}]`, then `exact {hp}`."
    rw [← hpath]
    exact hp

Conclusion "
`ext` works for any two sets, not just languages: sets of states too.
"

end Automata
