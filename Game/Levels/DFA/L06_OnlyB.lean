import Game.Levels.DFA.L05_FlipFlip

World "DFA"
Level 6
Title "Reading only b"

namespace Automata

Introduction "
Reading `b` never changes the state of `parityA`, so reading `b` any number of
times shouldn't either. `List.replicate n .b` is the string of `n` copies of `b`.

To prove something for every `n`, use **induction**. `induction' n with n ih`
leaves two goals:

* first, prove it for `n = 0`;
* then, assuming it holds for `n` (the hypothesis `ih`), prove it for `n + 1`.

The theorem `List.replicate_succ` says `List.replicate (n + 1) a = a :: List.replicate n a`.
"

/-- `parityA.evalFrom q (List.replicate n .b) = q` -/
TheoremDoc Automata.parityA_replicate_b as "parityA_replicate_b" in "DFA"
TheoremTab "DFA"

/-- Reading only `b`s leaves `parityA` where it started. -/
Statement parityA_replicate_b (q : Parity) (n : ℕ) :
    parityA.evalFrom q (List.replicate n .b) = q := by
  Hint "Use `induction' {n} with n ih`."
  induction' n with n ih
  · Hint "With no symbols at all, the machine stays in `{q}`. This is true by computation."
    rfl
  · Hint "`step` can't see a first symbol in `List.replicate ({n} + 1) AB.b` yet.
    Make it visible with `rw [List.replicate_succ]`."
    rw [List.replicate_succ]
    Hint "Now read the first `b`."
    step
    Hint "This is exactly the induction hypothesis `{ih}`."
    exact ih

Conclusion "
Induction is how you prove things about strings of every length.
"

NewTactic induction'
NewTheorem List.replicate_succ

NewDefinition List.replicate

end Automata
