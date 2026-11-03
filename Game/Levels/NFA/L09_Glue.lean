import Game.Levels.NFA.L08_Stay

World "NFA"
Level 9
Title "Gluing paths"

namespace Automata

Introduction "
A path reading `u` from `p` to `q`, followed by a path reading `v` from `q` to `r`,
is a path reading `u ++ v` from `p` to `r`. This holds for every NFA.

Induct on `u`, letting the starting state `p` vary. You will need both
unfolding lemmas: `NFA.path_nil_iff` and `NFA.path_cons_iff`.
"

/-- `M.Path p u q → M.Path q v r → M.Path p (u ++ v) r` -/
TheoremDoc Automata.NFA.path_append as "NFA.path_append" in "NFA"
TheoremTab "NFA"

/-- Two paths that meet can be glued into one. -/
Statement NFA.path_append {α σ : Type} {M : NFA α σ} {p q r : σ} {u v : List α}
    (h₁ : M.Path p u q) (h₂ : M.Path q v r) : M.Path p (u ++ v) r := by
  Hint "Induction on `{u}`, generalizing the start state:
  `induction' {u} with x xs ih generalizing {p}`."
  induction' u with x xs ih generalizing p
  · Hint "`{h₁}` reads nothing, so `{p} = {q}`. Get that equation with
    `rw [NFA.path_nil_iff] at {h₁}`."
    rw [NFA.path_nil_iff] at h₁
    Hint "Now rewrite the goal with `{h₁}` and use `{h₂}`."
    rw [h₁]
    exact h₂
  · Hint "Make the first symbol of the goal visible, then unfold the path:
    `rw [List.cons_append, NFA.path_cons_iff]`."
    rw [List.cons_append, NFA.path_cons_iff]
    Hint "Unfold `{h₁}` the same way, then take it apart."
    rw [NFA.path_cons_iff] at h₁
    obtain ⟨s, hs, hp⟩ := h₁
    Hint "The first move is `{hs}`; the induction hypothesis glues the rest:
    `exact ⟨{s}, {hs}, {ih} {hp}⟩`. (`{ih}` works out the start state from `{hp}`.)"
    exact ⟨s, hs, ih hp⟩

Conclusion "
The arguments of `NFA.path_append` are in curly braces in its statement: Lean
fills them in from the two paths you give it. So you can just write
`NFA.path_append h₁ h₂`.
"

end Automata
