import Game.Automata.Defs
import Game.Tactic.StepAttr
import Mathlib.Tactic.DeriveFintype

namespace Automata

/-- The two-letter alphabet `{a, b}`. -/
inductive AB | a | b
  deriving DecidableEq, Repr, Fintype

/-- States of the parity machine. -/
inductive Parity | even | odd
  deriving DecidableEq, Repr, Fintype

def Parity.flip : Parity → Parity
  | .even => .odd
  | .odd  => .even

/-- Accepts strings with an even number of `a`s. -/
def parityA : DFA AB Parity where
  step q x := match x with
    | .a => q.flip
    | .b => q
  start  := .even
  accept := {.even}

@[step_simp] theorem Parity.flip_even : Parity.even.flip = .odd := rfl
@[step_simp] theorem Parity.flip_odd : Parity.odd.flip = .even := rfl
@[step_simp] theorem parityA_start : parityA.start = .even := rfl
@[step_simp] theorem parityA_step_a (q : Parity) : parityA.step q .a = q.flip := rfl
@[step_simp] theorem parityA_step_b (q : Parity) : parityA.step q .b = q := rfl

instance : DecidablePred (· ∈ parityA.accept) :=
  fun q => inferInstanceAs (Decidable (q = .even))

/-- States of `containsAB`. -/
inductive ABState | s0 | s1 | s2
  deriving DecidableEq, Repr, Fintype

/-- The moves of `containsAB`: `abMove p x q = true` when it may go from `p` to `q` reading `x`. -/
def abMove : ABState → AB → ABState → Bool
  | .s0, _,  .s0 => true
  | .s0, .a, .s1 => true
  | .s1, .b, .s2 => true
  | .s2, _,  .s2 => true
  | _,   _,  _   => false

/-- Accepts the strings containing `ab`: wait in `s0`, guess where `ab` starts,
read it, then wait in `s2`. -/
def containsAB : NFA AB ABState where
  step p x := {q | abMove p x q = true}
  start := .s0
  accept := {.s2}

/-- The language `{aⁿbⁿ | n ∈ ℕ}`: some `a`s followed by the same number of `b`s. -/
def anbn : Lang AB := {w | ∃ n, w = List.replicate n .a ++ List.replicate n .b}

/-- The strings with as many `a`s as `b`s. -/
def balanced : Lang AB := {w | w.count .a = w.count .b}

end Automata
