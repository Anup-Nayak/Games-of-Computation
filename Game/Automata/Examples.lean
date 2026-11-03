import Game.Automata.Defs

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

instance : DecidablePred (· ∈ parityA.accept) :=
  fun q => inferInstanceAs (Decidable (q = .even))

end Automata
