import Game.Automata.Defs
import Mathlib.Tactic

/-! Spike: World 3. Not imported by the game; a check that the definitions support these proofs. -/

namespace Automata
namespace DFA
variable {α σ σ₁ σ₂ : Type}

def compl (M : DFA α σ) : DFA α σ :=
  { M with accept := M.acceptᶜ }

theorem compl_evalFrom (M : DFA α σ) (q : σ) (w : List α) :
    M.compl.evalFrom q w = M.evalFrom q w := by
  induction w generalizing q with
  | nil => rfl
  | cons x xs ih => exact ih (M.step q x)

theorem compl_accepts (M : DFA α σ) : M.compl.accepts = M.acceptsᶜ := by
  ext w
  simp only [mem_accepts, Set.mem_compl_iff, compl_evalFrom]
  rfl

/-- Run two machines side by side. Accepting set chosen by the caller. -/
def prod (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) (acc : Set (σ₁ × σ₂)) : DFA α (σ₁ × σ₂) where
  step s x := (M₁.step s.1 x, M₂.step s.2 x)
  start := (M₁.start, M₂.start)
  accept := acc

theorem prod_evalFrom (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) (acc) (p : σ₁) (q : σ₂) (w : List α) :
    (M₁.prod M₂ acc).evalFrom (p, q) w = (M₁.evalFrom p w, M₂.evalFrom q w) := by
  induction w generalizing p q with
  | nil => rfl
  | cons x xs ih => exact ih (M₁.step p x) (M₂.step q x)

def inter (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) : DFA α (σ₁ × σ₂) :=
  M₁.prod M₂ {s | s.1 ∈ M₁.accept ∧ s.2 ∈ M₂.accept}

def union (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) : DFA α (σ₁ × σ₂) :=
  M₁.prod M₂ {s | s.1 ∈ M₁.accept ∨ s.2 ∈ M₂.accept}

theorem inter_accepts (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) :
    (M₁.inter M₂).accepts = M₁.accepts ∩ M₂.accepts := by
  ext w
  simp only [mem_accepts, Set.mem_inter_iff]
  unfold inter
  rw [show (M₁.prod M₂ _).start = (M₁.start, M₂.start) from rfl, prod_evalFrom]
  rfl

theorem union_accepts (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) :
    (M₁.union M₂).accepts = M₁.accepts ∪ M₂.accepts := by
  ext w
  simp only [mem_accepts, Set.mem_union]
  unfold union
  rw [show (M₁.prod M₂ _).start = (M₁.start, M₂.start) from rfl, prod_evalFrom]
  rfl

end DFA

namespace Lang
variable {α : Type} {L L₁ L₂ : Lang α}

theorem IsRegular.compl (h : L.IsRegular) : (Lᶜ : Lang α).IsRegular := by
  obtain ⟨σ, hσ, M, rfl⟩ := h
  exact ⟨σ, hσ, M.compl, M.compl_accepts⟩

theorem IsRegular.inter (h₁ : L₁.IsRegular) (h₂ : L₂.IsRegular) :
    (L₁ ∩ L₂ : Lang α).IsRegular := by
  obtain ⟨σ₁, _, M₁, rfl⟩ := h₁
  obtain ⟨σ₂, _, M₂, rfl⟩ := h₂
  exact ⟨σ₁ × σ₂, inferInstance, M₁.inter M₂, M₁.inter_accepts M₂⟩

theorem IsRegular.union (h₁ : L₁.IsRegular) (h₂ : L₂.IsRegular) :
    (L₁ ∪ L₂ : Lang α).IsRegular := by
  obtain ⟨σ₁, _, M₁, rfl⟩ := h₁
  obtain ⟨σ₂, _, M₂, rfl⟩ := h₂
  exact ⟨σ₁ × σ₂, inferInstance, M₁.union M₂, M₁.union_accepts M₂⟩

/-- Capstone of World 3: no new machine, only earlier lemmas. -/
theorem IsRegular.symmDiff (h₁ : L₁.IsRegular) (h₂ : L₂.IsRegular) :
    ((L₁ ∩ L₂ᶜ) ∪ (L₂ ∩ L₁ᶜ) : Lang α).IsRegular :=
  (h₁.inter h₂.compl).union (h₂.inter h₁.compl)

end Lang
end Automata
