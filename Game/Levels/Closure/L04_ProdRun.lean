import Game.Levels.Closure.L03_RegCompl

World "Closure"
Level 4
Title "Two machines at once"

namespace Automata

Introduction "
To recognise `L₁ ∩ L₂`, run a machine for each **at the same time**. The product
machine `M₁.prod M₂ acc` has *pairs* of states `(p, q)`, and moves both:

```
(M₁.prod M₂ acc).step (p, q) x = (M₁.step p x, M₂.step q x)
```

The set `acc` says which pairs accept. You'll choose it in the next levels.

First: the product's run is the pair of the two runs.
"

/-- `(M₁.prod M₂ acc).evalFrom (p, q) w = (M₁.evalFrom p w, M₂.evalFrom q w)` -/
TheoremDoc Automata.DFA.prod_evalFrom as "DFA.prod_evalFrom" in "Closure"
TheoremTab "Closure"

/-- Running the product = running both machines. -/
Statement DFA.prod_evalFrom {α σ₁ σ₂ : Type} (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) (acc : Set (σ₁ × σ₂))
    (p : σ₁) (q : σ₂) (w : List α) :
    (M₁.prod M₂ acc).evalFrom (p, q) w = (M₁.evalFrom p w, M₂.evalFrom q w) := by
  Hint "Both starting states change as the machines read, so generalize both:
  `induction' {w} with x xs ih generalizing {p} {q}`."
  induction' w with x xs ih generalizing p q
  · rfl
  · Hint "Read the first symbol in all three runs: `step` three times."
    step
    step
    step
    Hint "`{ih}` takes both new states: `exact {ih} ({M₁}.step {p} {x}) ({M₂}.step {q} {x})`."
    exact ih (M₁.step p x) (M₂.step q x)

NewDefinition Automata.DFA.prod

end Automata
