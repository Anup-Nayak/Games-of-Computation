import Game.Levels.Closure.L06_Union

World "Closure"
Level 7
Title "Regular: intersection"

namespace Automata

Introduction "
The intersection of two regular languages is regular.

The product machine has states `σ₁ × σ₂`. You need to show that this is
finite. Lean knows that a product of finite types is finite: `inferInstance`
asks it to find that proof itself.
"

/-- `L₁.IsRegular → L₂.IsRegular → (L₁ ∩ L₂).IsRegular` -/
TheoremDoc Automata.Lang.IsRegular.inter as "Lang.IsRegular.inter" in "Closure"
TheoremTab "Closure"

/-- Regular languages are closed under intersection. -/
Statement Lang.IsRegular.inter {α : Type} {L₁ L₂ : Lang α}
    (h₁ : L₁.IsRegular) (h₂ : L₂.IsRegular) : (L₁ ∩ L₂ : Lang α).IsRegular := by
  Hint "Get both machines with `obtain`, using `rfl` as before."
  obtain ⟨σ₁, hσ₁, M₁, rfl⟩ := h₁
  obtain ⟨σ₂, hσ₂, M₂, rfl⟩ := h₂
  Hint "`exact ⟨{σ₁} × {σ₂}, inferInstance, {M₁}.inter {M₂}, DFA.inter_accepts {M₁} {M₂}⟩`"
  exact ⟨σ₁ × σ₂, inferInstance, M₁.inter M₂, DFA.inter_accepts M₁ M₂⟩

NewDefinition inferInstance

end Automata
