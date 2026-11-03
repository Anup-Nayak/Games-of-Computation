import Game.Levels.Closure.L08_RegUnion

World "Closure"
Level 9
Title "Symmetric difference"

namespace Automata

Introduction "
**Final level of this world.** The strings in exactly one of `L₁`, `L₂` form

`(L₁ ∩ L₂ᶜ) ∪ (L₂ ∩ L₁ᶜ)`.

Is this regular when `L₁` and `L₂` are? You don't need any new machine: the
three closure results you just proved are enough. Work from the outside in with
`apply`: the outermost operation is `∪`, so start with `apply Lang.IsRegular.union`.
"

/-- `L₁.IsRegular → L₂.IsRegular → ((L₁ ∩ L₂ᶜ) ∪ (L₂ ∩ L₁ᶜ)).IsRegular` -/
TheoremDoc Automata.Lang.IsRegular.symmDiff as "Lang.IsRegular.symmDiff" in "Closure"

/-- Regular languages are closed under symmetric difference. -/
Statement Lang.IsRegular.symmDiff {α : Type} {L₁ L₂ : Lang α}
    (h₁ : L₁.IsRegular) (h₂ : L₂.IsRegular) :
    ((L₁ ∩ L₂ᶜ) ∪ (L₂ ∩ L₁ᶜ) : Lang α).IsRegular := by
  Hint "The outermost operation is `∪`: `apply Lang.IsRegular.union`."
  apply Lang.IsRegular.union
  · Hint "Now an intersection."
    apply Lang.IsRegular.inter
    · exact h₁
    · Hint "And a complement."
      apply Lang.IsRegular.compl
      exact h₂
  · apply Lang.IsRegular.inter
    · exact h₂
    · apply Lang.IsRegular.compl
      exact h₁

Conclusion "
**World complete.** Regular languages are closed under complement,
intersection and union, and therefore under any combination of them.

The whole last proof also fits on one line:
`exact (h₁.inter h₂.compl).union (h₂.inter h₁.compl)`.
Each closure result is a function from *regular* to *regular*, and you
composed them.
"

end Automata
