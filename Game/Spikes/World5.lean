import Game.Spikes.World1
import Mathlib.Tactic

/-! Spike: World 5. Not imported by the game; a check that the definitions support these proofs. -/

namespace Automata
variable {α σ : Type}

/-- Level: prefixes reaching the same state cannot be told apart. -/
theorem same_state_indist (M : DFA α σ) {u v : List α}
    (h : M.evalFrom M.start u = M.evalFrom M.start v) (w : List α) :
    u ++ w ∈ M.accepts ↔ v ++ w ∈ M.accepts := by
  simp only [DFA.mem_accepts, evalFrom_append, h]

/-- Level: pigeonhole — infinitely many prefixes, finitely many states. -/
theorem exists_collision [Finite σ] (M : DFA α σ) (f : ℕ → List α) :
    ∃ i j, i ≠ j ∧ M.evalFrom M.start (f i) = M.evalFrom M.start (f j) :=
  Finite.exists_ne_map_eq_of_infinite (fun n => M.evalFrom M.start (f n))

def anbn : Lang AB := {w | ∃ n, w = List.replicate n .a ++ List.replicate n .b}

/-- Level: counting letters pins down the exponents. -/
theorem replicate_eq {i j n : ℕ}
    (h : List.replicate i AB.a ++ List.replicate j AB.b =
         List.replicate n AB.a ++ List.replicate n AB.b) : i = j := by
  have ha := congrArg (List.count AB.a) h
  have hb := congrArg (List.count AB.b) h
  simp [List.count_replicate] at ha hb
  omega

/-- Boss level. -/
theorem anbn_not_regular : ¬ anbn.IsRegular := by
  rintro ⟨σ, hσ, M, hM⟩
  obtain ⟨i, j, hij, hcol⟩ := exists_collision M (fun n => List.replicate n AB.a)
  have hi : List.replicate i AB.a ++ List.replicate i AB.b ∈ M.accepts := by
    rw [hM]; exact ⟨i, rfl⟩
  have hj := (same_state_indist M hcol _).1 hi
  rw [hM] at hj
  obtain ⟨n, hn⟩ := hj
  exact hij (replicate_eq hn).symm

end Automata
