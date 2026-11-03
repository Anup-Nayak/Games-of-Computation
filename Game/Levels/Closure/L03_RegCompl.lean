import Game.Levels.Closure.L02_ComplAccepts

World "Closure"
Level 3
Title "Regular languages"

namespace Automata

Introduction "
A language is **regular** if some DFA with finitely many states recognises it:

```
def Lang.IsRegular (L : Lang α) : Prop :=
  ∃ (σ : Type) (_ : Finite σ) (M : DFA α σ), M.accepts = L
```

So the complement of a regular language is regular: take its machine and use `compl`.

A handy trick with `obtain`: writing `rfl` in place of the last name, as in
`obtain ⟨σ, hσ, M, rfl⟩ := h`, *substitutes* the equation `M.accepts = L`, so
`L` gets replaced by `M.accepts` everywhere.
"

/-- `L.IsRegular → Lᶜ.IsRegular` -/
TheoremDoc Automata.Lang.IsRegular.compl as "Lang.IsRegular.compl" in "Closure"
TheoremTab "Closure"

/-- Regular languages are closed under complement. -/
Statement Lang.IsRegular.compl {α : Type} {L : Lang α} (h : L.IsRegular) :
    (Lᶜ : Lang α).IsRegular := by
  Hint "Get the machine for `{L}`: `obtain ⟨σ, hσ, M, rfl⟩ := {h}`."
  obtain ⟨σ, hσ, M, rfl⟩ := h
  Hint "Same states, the complement machine, and the last level's theorem:
  `exact ⟨{σ}, {hσ}, {M}.compl, DFA.compl_accepts {M}⟩`."
  exact ⟨σ, hσ, M.compl, DFA.compl_accepts M⟩

Conclusion "
Each closure property has this shape: a construction on machines, a proof
that it works, and a short wrap-up about regular languages.
"

NewDefinition Automata.Lang.IsRegular

end Automata
