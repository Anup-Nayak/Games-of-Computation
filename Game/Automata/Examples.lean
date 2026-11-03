import Game.Automata.Defs
import Game.Tactic.StepAttr

namespace Automata

/-- The two-letter alphabet `{a, b}`. -/
inductive AB | a | b
  deriving DecidableEq, Repr

/-- States of the parity machine. -/
inductive Parity | even | odd
  deriving DecidableEq, Repr

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

end Automata
