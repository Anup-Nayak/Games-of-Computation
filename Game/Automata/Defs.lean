import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Count
import Mathlib.Data.Finite.Defs

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

end NFA

/-! ## Regular languages -/

/-- A language is regular if some DFA with finitely many states accepts it. -/
def Lang.IsRegular {α : Type} (L : Lang α) : Prop :=
  ∃ (σ : Type) (_ : Finite σ) (M : DFA α σ), M.accepts = L

end Automata
