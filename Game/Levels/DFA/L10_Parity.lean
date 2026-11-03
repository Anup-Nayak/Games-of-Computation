import Game.Levels.DFA.L09_IfThenElse

World "DFA"
Level 10
Title "Where the machine ends up"

namespace Automata

Introduction "
Time to describe `parityA` on **every** string and **every** starting state:
it ends where it started if the string has an even number of `a`s, and in the
other state otherwise.

`w.count .a` is the number of `a`s in `w`. Two theorems describe it:

* `List.count_cons_self : (a :: l).count a = l.count a + 1`
* `List.count_cons_of_ne : b ≠ a → (b :: l).count a = l.count a`

You'll need induction with `generalizing`, `cases` on the first symbol, `step`,
and the result `ite_flip_succ` from the last level.
"

/-- `parityA.evalFrom q w = if w.count .a % 2 = 0 then q else q.flip` -/
TheoremDoc Automata.parityA_evalFrom as "parityA_evalFrom" in "DFA"
TheoremTab "DFA"

/-- `parityA` ends in `q` after an even number of `a`s, and in `q.flip` otherwise. -/
Statement parityA_evalFrom (q : Parity) (w : List AB) :
    parityA.evalFrom q w = if w.count .a % 2 = 0 then q else q.flip := by
  Hint "Induction on `{w}`. The state changes with every `a`, so generalize `{q}`:
  `induction' {w} with x xs ih generalizing {q}`."
  induction' w with x xs ih generalizing q
  · Hint "The empty string has no `a`s, so both sides compute to `{q}`."
    rfl
  · Hint "What happens depends on the first symbol. Split with `cases {x}`."
    cases x
    · Hint "First symbol `a`: read it with `step`."
      step
      Hint "Use the induction hypothesis to rewrite the run on the left, and
      `List.count_cons_self` to count the `a` on the right:
      `rw [{ih}, List.count_cons_self]`."
      rw [ih, List.count_cons_self]
      Hint "This is exactly `ite_flip_succ`."
      exact ite_flip_succ _ q
    · Hint "First symbol `b`: read it with `step`."
      step
      Hint "Rewrite the run with `{ih}`. On the right, the `b` doesn't change
      the count: `List.count_cons_of_ne` needs a proof of `AB.b ≠ AB.a`, which
      `decide` provides. Try `rw [{ih}, List.count_cons_of_ne (by decide)]`."
      rw [ih, List.count_cons_of_ne (by decide)]

Conclusion "
You now know *exactly* what `parityA` does on every input. One last step:
turn this into a description of the language it accepts.
"

NewTheorem List.count_cons_self List.count_cons_of_ne

end Automata
