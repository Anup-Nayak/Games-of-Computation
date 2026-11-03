import Game.Levels.Closure.L07_RegInter

World "Closure"
Level 8
Title "Regular: union"

namespace Automata

Introduction "
The union of two regular languages is regular.
"

/-- `L₁.IsRegular → L₂.IsRegular → (L₁ ∪ L₂).IsRegular` -/
TheoremDoc Automata.Lang.IsRegular.union as "Lang.IsRegular.union" in "Closure"
TheoremTab "Closure"

/-- Regular languages are closed under union. -/
Statement Lang.IsRegular.union {α : Type} {L₁ L₂ : Lang α}
    (h₁ : L₁.IsRegular) (h₂ : L₂.IsRegular) : (L₁ ∪ L₂ : Lang α).IsRegular := by
  Hint (hidden := true) "Exactly like the last level, with `DFA.union`."
  obtain ⟨σ₁, hσ₁, M₁, rfl⟩ := h₁
  obtain ⟨σ₂, hσ₂, M₂, rfl⟩ := h₂
  exact ⟨σ₁ × σ₂, inferInstance, M₁.union M₂, DFA.union_accepts M₁ M₂⟩

end Automata
