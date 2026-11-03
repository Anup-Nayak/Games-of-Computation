import Game.Levels.NonRegular.L05_Exponents

World "NonRegular"
Level 6
Title "aⁿbⁿ is not regular"

namespace Automata

Introduction "
**Boss level.** The language `anbn = {aⁿbⁿ | n ∈ ℕ}` is **not regular**: no DFA
recognises it.

The plan. Suppose a finite DFA `M` did.

1. By pigeonhole, `aⁱ` and `aʲ` reach the same state for some `i ≠ j`.
2. `aⁱbⁱ` is in the language, so `M` accepts it.
3. `M` can't tell `aⁱ` from `aʲ`, so it also accepts `aʲbⁱ`.
4. But `aʲbⁱ` is not of the form `aⁿbⁿ`, since `j ≠ i`. Contradiction!

For an iff `h : A ↔ B`, `h.1` is the direction `A → B`.
"

/-- `¬ anbn.IsRegular` -/
TheoremDoc Automata.anbn_not_regular as "anbn_not_regular" in "NonRegular"
TheoremTab "NonRegular"

/-- No DFA recognises `{aⁿbⁿ}`. -/
Statement anbn_not_regular : ¬ anbn.IsRegular := by
  Hint "Suppose it were regular: `intro h`, then get the machine with
  `obtain ⟨σ, hσ, M, hM⟩ := h`."
  intro h
  obtain ⟨σ, hσ, M, hM⟩ := h
  Hint "Step 1, pigeonhole on powers of `a`:
  `obtain ⟨i, j, hij, hcol⟩ := exists_collision {M} AB.a`."
  obtain ⟨i, j, hij, hcol⟩ := exists_collision M AB.a
  Hint "Step 2: `have hi : List.replicate {i} AB.a ++ List.replicate {i} AB.b ∈ {M}.accepts := by ...`
  Inside, use `{hM}` to switch to `anbn`, then give `n = {i}`."
  have hi : List.replicate i AB.a ++ List.replicate i AB.b ∈ M.accepts := by
    rw [hM]
    exact ⟨i, rfl⟩
  Hint "Step 3: `{M}` can't tell `aⁱ` from `aʲ`:
  `have hj := (same_state_indist {M} {hcol} _).1 {hi}`."
  have hj := (same_state_indist M hcol _).1 hi
  Hint "Step 4: so `aʲbⁱ` would be in `anbn`. Switch back with `rw [{hM}] at {hj}`,
  and take it apart."
  rw [hM] at hj
  obtain ⟨n, hn⟩ := hj
  Hint "Read off the exponents with `have := replicate_eq {hn}`, and `omega`
  finds the contradiction with `{hij}`."
  have := replicate_eq hn
  omega

Conclusion "
A DFA can't count without bound. To check `aⁿbⁿ` it would need to remember `n`,
and finitely many states can only remember so much.
"

NewDefinition Automata.anbn

end Automata
