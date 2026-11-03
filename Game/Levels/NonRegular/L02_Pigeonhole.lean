import Game.Levels.NonRegular.L01_Indist

World "NonRegular"
Level 2
Title "The pigeonhole principle"

namespace Automata

Introduction "
Feed a DFA the strings `ε, x, xx, xxx, …`, infinitely many. It has only finitely
many states, so two of these strings must end in the same state. This is the
**pigeonhole principle**: more pigeons than holes means two share a hole.

Mathlib has it as

`Finite.exists_ne_map_eq_of_infinite (f : α → β) : ∃ i j, i ≠ j ∧ f i = f j`

for any function `f` from an infinite type `α` to a finite type `β`.

`fun n => ...` writes a function: `fun n => M.evalFrom M.start (List.replicate n x)`
sends `n` to the state after reading `x` `n` times.
"

/-- `∃ i j, i ≠ j ∧ M.evalFrom M.start (List.replicate i x) = M.evalFrom M.start (List.replicate j x)` -/
TheoremDoc Automata.exists_collision as "exists_collision" in "NonRegular"
TheoremTab "NonRegular"

/-- A finite DFA sends two different powers `xⁱ`, `xʲ` to the same state. -/
Statement exists_collision {α σ : Type} [Finite σ] (M : DFA α σ) (x : α) :
    ∃ i j, i ≠ j ∧ M.evalFrom M.start (List.replicate i x) =
      M.evalFrom M.start (List.replicate j x) := by
  Hint "Apply the pigeonhole principle to the function
  `fun n => {M}.evalFrom {M}.start (List.replicate n {x})`, from `ℕ` (infinite)
  to `{σ}` (finite):
  `exact Finite.exists_ne_map_eq_of_infinite (fun n => {M}.evalFrom {M}.start (List.replicate n {x}))`"
  exact Finite.exists_ne_map_eq_of_infinite (fun n => M.evalFrom M.start (List.replicate n x))

Conclusion "
Finite memory, infinitely many strings: some information must be lost.
"

NewTheorem Finite.exists_ne_map_eq_of_infinite

end Automata
