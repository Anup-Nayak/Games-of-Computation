import Game.Levels.Closure.L05_Inter

World "Closure"
Level 6
Title "Union"

namespace Automata

Introduction "
Same product, different verdict: `M₁.union M₂` accepts when **at least one**
machine accepts. `Set.mem_union : w ∈ L₁ ∪ L₂ ↔ w ∈ L₁ ∨ w ∈ L₂`.
"

/-- `(M₁.union M₂).accepts = M₁.accepts ∪ M₂.accepts` -/
TheoremDoc Automata.DFA.union_accepts as "DFA.union_accepts" in "Closure"
TheoremTab "Closure"

/-- The union machine recognises the union. -/
Statement DFA.union_accepts {α σ₁ σ₂ : Type} (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) :
    (M₁.union M₂).accepts = M₁.accepts ∪ M₂.accepts := by
  ext w
  Hint (hidden := true) "Exactly like the last level, with `Set.mem_union` and
  `DFA.union`."
  rw [Set.mem_union, DFA.mem_accepts, DFA.mem_accepts, DFA.mem_accepts]
  unfold DFA.union
  rw [DFA.prod_start, DFA.prod_evalFrom]
  rfl

NewTheorem Set.mem_union
NewDefinition Automata.DFA.union

end Automata
