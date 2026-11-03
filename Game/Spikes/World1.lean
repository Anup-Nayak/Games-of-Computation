import Game.Automata.Examples
import Mathlib.Tactic

/-! Spike: World 1. Not imported by the game; a check that the definitions support these proofs. -/

namespace Automata
open DFA

-- `decide` works on concrete strings
example : [AB.a, .b, .a] ∈ parityA.accepts := by decide
example : [AB.a, .b] ∉ parityA.accepts := by decide

theorem evalFrom_append {α σ : Type} (M : DFA α σ) (q : σ) (u v : List α) :
    M.evalFrom q (u ++ v) = M.evalFrom (M.evalFrom q u) v := by
  induction u generalizing q with
  | nil => rfl
  | cons x xs ih => exact ih (M.step q x)

theorem Parity.flip_flip (q : Parity) : q.flip.flip = q := by
  cases q <;> rfl

theorem parity_evalFrom (q : Parity) (w : List AB) :
    parityA.evalFrom q w = if w.count .a % 2 = 0 then q else q.flip := by
  induction w generalizing q with
  | nil => rfl
  | cons x xs ih =>
    rw [evalFrom_cons, ih]
    cases x with
    | a =>
      show (if xs.count .a % 2 = 0 then q.flip else q.flip.flip) = _
      rw [List.count_cons_self, Parity.flip_flip]
      by_cases h : xs.count .a % 2 = 0
      · have : (xs.count .a + 1) % 2 ≠ 0 := by omega
        simp [h, this]
      · have : (xs.count .a + 1) % 2 = 0 := by omega
        simp [h, this]
    | b =>
      show (if xs.count .a % 2 = 0 then q else q.flip) = _
      rw [List.count_cons_of_ne (by decide)]

theorem parityA_accepts : parityA.accepts = {w | w.count .a % 2 = 0} := by
  ext w
  rw [mem_accepts, parity_evalFrom]
  by_cases h : w.count .a % 2 = 0
  · simp [h, parityA]
  · simp [h, parityA, Parity.flip]

end Automata
