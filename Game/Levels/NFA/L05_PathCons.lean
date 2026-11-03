import Game.Levels.NFA.L04_PathNil

World "NFA"
Level 5
Title "Taking a path apart: one move"

namespace Automata

Introduction "
A path reading `x :: xs` must have come from the `cons` rule: a first allowed
move to some state `q`, and a path from `q` reading the rest.

You can take apart an assumption `h : M.Path p (x :: xs) r` with
`obtain _ | ⟨hq, hp⟩ := h`. The pattern has one slot per rule: `_` for `nil`
(which can't apply, so Lean skips it) and `⟨hq, hp⟩` for the two facts `cons`
needs.
"

/-- `M.Path p (x :: xs) r ↔ ∃ q ∈ M.step p x, M.Path q xs r` -/
TheoremDoc Automata.NFA.path_cons_iff as "NFA.path_cons_iff" in "NFA"
TheoremTab "NFA"

/-- A path reading `x :: xs` is a first move followed by a path reading `xs`. -/
Statement NFA.path_cons_iff {α σ : Type} (M : NFA α σ) (p r : σ) (x : α) (xs : List α) :
    M.Path p (x :: xs) r ↔ ∃ q ∈ M.step p x, M.Path q xs r := by
  constructor
  · intro h
    Hint "Take `{h}` apart: `obtain _ | ⟨hq, hp⟩ := {h}`."
    obtain _ | ⟨hq, hp⟩ := h
    Hint "The middle state has no name you can type, but Lean can fill it in:
    `exact ⟨_, {hq}, {hp}⟩`."
    exact ⟨_, hq, hp⟩
  · intro h
    Hint (hidden := true) "Take the `∃` apart with `obtain ⟨q, hq, hp⟩ := {h}`,
    then build the path with the `cons` rule."
    obtain ⟨q, hq, hp⟩ := h
    exact NFA.Path.cons hq hp

Conclusion "
With `NFA.path_nil_iff` and `NFA.path_cons_iff` you can rewrite *any* statement
about paths into plain logic, one symbol at a time.
"

end Automata
