import Game.Levels.DFA.L08_Omega

World "DFA"
Level 9
Title "If-then-else"

namespace Automata

Introduction "
The answer to *where does `parityA` end up* depends on a condition:
`if c then x else y`.

To reason about it, split on whether the condition holds:
`by_cases h : c` gives one goal with `h : c` and one with `h : ¬ c`.
Then `if_pos h` and `if_neg h` rewrite the `if` away:

* `if_pos : c → (if c then x else y) = x`
* `if_neg : ¬ c → (if c then x else y) = y`

This level is the key step for the next one.
"

/-- `(if n % 2 = 0 then q.flip else q.flip.flip) = if (n + 1) % 2 = 0 then q else q.flip` -/
TheoremDoc Automata.ite_flip_succ as "ite_flip_succ" in "DFA"
TheoremTab "Logic"

/-- One more `a` swaps the outcome. -/
Statement ite_flip_succ (n : ℕ) (q : Parity) :
    (if n % 2 = 0 then q.flip else q.flip.flip) = if (n + 1) % 2 = 0 then q else q.flip := by
  Hint "Split on the condition on the left: `by_cases h : {n} % 2 = 0`."
  by_cases h : n % 2 = 0
  · Hint "The left `if` takes its first branch: `rw [if_pos {h}]`.
    On the right, `({n} + 1) % 2 = 0` is false. You can prove that inside the
    rewrite: `rw [if_pos {h}, if_neg (by omega)]`."
    rw [if_pos h, if_neg (by omega)]
  · Hint "Now the left `if` takes its second branch, and the right one its first."
    rw [if_neg h, if_pos (by omega)]
    Hint (hidden := true) "You proved `Parity.flip_flip` earlier."
    rw [Parity.flip_flip]

Conclusion "
`rw` closes the goal by itself when both sides become identical.
"

NewTactic by_cases
NewTheorem if_pos if_neg

end Automata
