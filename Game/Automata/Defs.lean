import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Count
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Pigeonhole
import Game.Tactic.StepAttr

namespace Automata

/-- A language over the alphabet `α` is a set of strings. -/
abbrev Lang (α : Type) := Set (List α)

/-- `L.concat M`: strings that split as a string of `L` followed by a string of `M`. -/
def Lang.concat {α : Type} (L M : Lang α) : Lang α :=
  {w | ∃ u ∈ L, ∃ v ∈ M, w = u ++ v}

/-! ## Deterministic finite automata -/

structure DFA (α σ : Type) where
  step   : σ → α → σ
  start  : σ
  accept : Set σ

namespace DFA
variable {α σ : Type}

/-- The state reached by reading `w` starting from `q`. -/
def evalFrom (M : DFA α σ) (q : σ) : List α → σ
  | []      => q
  | x :: xs => M.evalFrom (M.step q x) xs

/-- The language accepted by `M`. -/
def accepts (M : DFA α σ) : Lang α := {w | M.evalFrom M.start w ∈ M.accept}

theorem evalFrom_nil (M : DFA α σ) (q : σ) : M.evalFrom q [] = q := rfl

theorem evalFrom_cons (M : DFA α σ) (q : σ) (x : α) (xs : List α) :
    M.evalFrom q (x :: xs) = M.evalFrom (M.step q x) xs := rfl

theorem mem_accepts (M : DFA α σ) (w : List α) :
    w ∈ M.accepts ↔ M.evalFrom M.start w ∈ M.accept := Iff.rfl

/-- Acceptance of a concrete string is decidable when the accept set is. -/
instance (M : DFA α σ) [DecidablePred (· ∈ M.accept)] (w : List α) :
    Decidable (w ∈ M.accepts) :=
  inferInstanceAs (Decidable (M.evalFrom M.start w ∈ M.accept))

end DFA

/-! ## Nondeterministic finite automata -/

structure NFA (α σ : Type) where
  step   : σ → α → Set σ
  start  : σ
  accept : Set σ

namespace NFA
variable {α σ : Type}

/-- `M.Path p w r`: reading `w` can lead from `p` to `r`. -/
inductive Path (M : NFA α σ) : σ → List α → σ → Prop
  | nil (q : σ) : Path M q [] q
  | cons {p q r : σ} {x : α} {xs : List α} :
      q ∈ M.step p x → Path M q xs r → Path M p (x :: xs) r

def accepts (M : NFA α σ) : Lang α := {w | ∃ f ∈ M.accept, M.Path M.start w f}

theorem mem_accepts (M : NFA α σ) (w : List α) :
    w ∈ M.accepts ↔ ∃ f ∈ M.accept, M.Path M.start w f := Iff.rfl

end NFA

/-! ## Constructions on DFAs -/

namespace DFA
variable {α σ σ₁ σ₂ : Type}

/-- View a DFA as an NFA with exactly one possible move each time. -/
def toNFA (M : DFA α σ) : NFA α σ where
  step q x := {M.step q x}
  start := M.start
  accept := M.accept

theorem mem_toNFA_step (M : DFA α σ) (p q : σ) (x : α) :
    q ∈ M.toNFA.step p x ↔ q = M.step p x := Iff.rfl
theorem toNFA_start (M : DFA α σ) : M.toNFA.start = M.start := rfl
theorem toNFA_accept (M : DFA α σ) : M.toNFA.accept = M.accept := rfl

/-- Same machine, opposite verdict: accept exactly where `M` rejects. -/
def compl (M : DFA α σ) : DFA α σ :=
  { M with accept := M.acceptᶜ }

@[step_simp] theorem compl_step (M : DFA α σ) : M.compl.step = M.step := rfl
theorem compl_start (M : DFA α σ) : M.compl.start = M.start := rfl

/-- Run `M₁` and `M₂` side by side; accept in the states `acc`. -/
def prod (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) (acc : Set (σ₁ × σ₂)) : DFA α (σ₁ × σ₂) where
  step s x := (M₁.step s.1 x, M₂.step s.2 x)
  start := (M₁.start, M₂.start)
  accept := acc

@[step_simp] theorem prod_step (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) (acc) (s : σ₁ × σ₂) (x : α) :
    (M₁.prod M₂ acc).step s x = (M₁.step s.1 x, M₂.step s.2 x) := rfl
theorem prod_start (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) (acc) :
    (M₁.prod M₂ acc).start = (M₁.start, M₂.start) := rfl

/-- Accept when both machines accept. -/
def inter (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) : DFA α (σ₁ × σ₂) :=
  M₁.prod M₂ {s | s.1 ∈ M₁.accept ∧ s.2 ∈ M₂.accept}

/-- Accept when at least one machine accepts. -/
def union (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) : DFA α (σ₁ × σ₂) :=
  M₁.prod M₂ {s | s.1 ∈ M₁.accept ∨ s.2 ∈ M₂.accept}

end DFA

/-! ## The subset construction -/

namespace NFA
variable {α σ : Type}

/-- The subset construction: a DFA whose states are *sets* of states of `M`,
tracking every state `M` could be in. -/
def toDFA (M : NFA α σ) : DFA α (Set σ) where
  step S x := {r | ∃ p ∈ S, r ∈ M.step p x}
  start := {M.start}
  accept := {S | ∃ q ∈ S, q ∈ M.accept}

@[step_simp] theorem toDFA_step (M : NFA α σ) (S : Set σ) (x : α) :
    M.toDFA.step S x = {r | ∃ p ∈ S, r ∈ M.step p x} := rfl
theorem toDFA_start (M : NFA α σ) : M.toDFA.start = {M.start} := rfl

end NFA

/-! ## Regular languages -/

/-- A language is regular if some DFA with finitely many states accepts it. -/
def Lang.IsRegular {α : Type} (L : Lang α) : Prop :=
  ∃ (σ : Type) (_ : Finite σ) (M : DFA α σ), M.accepts = L

end Automata
