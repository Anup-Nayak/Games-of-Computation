import Game.Levels.Closure.L04_ProdRun

World "Closure"
Level 5
Title "Intersection"

namespace Automata

Introduction "
`M₁.inter M₂` is the product that accepts when **both** machines accept:

```
def DFA.inter (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) :=
  M₁.prod M₂ {s | s.1 ∈ M₁.accept ∧ s.2 ∈ M₂.accept}
```

(`s.1` and `s.2` are the two components of the pair `s`.)

`unfold DFA.inter` replaces `M₁.inter M₂` by its definition, so that theorems
about `prod` apply. You'll also want `DFA.prod_start`:
`(M₁.prod M₂ acc).start = (M₁.start, M₂.start)`.
"

/-- `(M₁.inter M₂).accepts = M₁.accepts ∩ M₂.accepts` -/
TheoremDoc Automata.DFA.inter_accepts as "DFA.inter_accepts" in "Closure"
TheoremTab "Closure"

/-- The intersection machine recognises the intersection. -/
Statement DFA.inter_accepts {α σ₁ σ₂ : Type} (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) :
    (M₁.inter M₂).accepts = M₁.accepts ∩ M₂.accepts := by
  ext w
  Hint "Unfold the intersection of languages and all three acceptances:
  `rw [Set.mem_inter_iff, DFA.mem_accepts, DFA.mem_accepts, DFA.mem_accepts]`."
  rw [Set.mem_inter_iff, DFA.mem_accepts, DFA.mem_accepts, DFA.mem_accepts]
  Hint "Now see the product inside: `unfold DFA.inter`."
  unfold DFA.inter
  Hint "Rewrite the start state and the run:
  `rw [DFA.prod_start, DFA.prod_evalFrom]`."
  rw [DFA.prod_start, DFA.prod_evalFrom]
  Hint "Both sides now say the same thing, by definition of the accepting set."
  rfl

NewTactic unfold
NewTheorem Set.mem_inter_iff Automata.DFA.prod_start
NewDefinition Automata.DFA.inter

end Automata
