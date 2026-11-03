import Game.Levels.Subset.L05_OneSymbol

World "Subset"
Level 6
Title "Strengthening the induction"

namespace Automata

Introduction "
Third step: put the two together by induction on `w`.

You only care about starting from `{M.start}`. But after the first symbol the
subset machine is in some *other* set, so an induction hypothesis about
`{M.start}` alone would be useless. That's why the statement is about **every**
starting set `S`, and why you need `generalizing S`.

Proving a *stronger* statement can make the induction *easier*: the hypothesis
you get is stronger too.

(Here, use `rw [DFA.evalFrom_cons]` rather than `step`. `step` would also
expand the next set into its definition, which the next rewrite doesn't want.)
"

/-- `M.toDFA.evalFrom S w = {r | ∃ p ∈ S, M.Path p w r}` -/
TheoremDoc Automata.NFA.toDFA_evalFrom as "NFA.toDFA_evalFrom" in "Subset"
TheoremTab "Subset"

/-- The subset machine is in exactly the set of states reachable by a path. -/
Statement NFA.toDFA_evalFrom {α σ : Type} (M : NFA α σ) (S : Set σ) (w : List α) :
    M.toDFA.evalFrom S w = {r | ∃ p ∈ S, M.Path p w r} := by
  Hint "`induction' {w} with x xs ih generalizing {S}`"
  Branch
    induction' w with x xs ih
    · exact NFA.toDFA_evalFrom_nil M S
    rw [DFA.evalFrom_cons]
    Hint "Stuck: `{ih}` is about starting from `{S}`, but the machine now starts
    from the next set. Undo with **Retry** and add `generalizing S`."
  induction' w with x xs ih generalizing S
  · Hint "This is the first step you proved."
    exact NFA.toDFA_evalFrom_nil M S
  · Hint "Read the first symbol: `rw [DFA.evalFrom_cons]`. Then `{ih}` works for
    the next set: `rw [{ih}]`."
    rw [DFA.evalFrom_cons, ih]
    Hint "This is the second step you proved."
    exact NFA.toDFA_onestep M S x xs

Conclusion "
This is the heart of the subset construction. The rest is bookkeeping.
"

end Automata
