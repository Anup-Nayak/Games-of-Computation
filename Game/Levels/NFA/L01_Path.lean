import Game.Metadata

World "NFA"
Level 1
Title "Machines that guess"

namespace Automata

Introduction "
A **nondeterministic** finite automaton (NFA) may have *several* possible moves
for a symbol, or none at all. `M.step p x` is now a **set** of states: all the
places `M` may go from `p` reading `x`.

So there is no single run any more. Instead we talk about **paths**.
`M.Path p w r` says: reading `w`, the machine *can* get from `p` to `r`.
It is built by two rules:

* `NFA.Path.nil q : M.Path q [] q`: reading nothing, you stay where you are;
* `NFA.Path.cons : q ∈ M.step p x → M.Path q xs r → M.Path p (x :: xs) r`:
  make one allowed move to `q`, then continue.

`M.Path` is an **inductive proposition**: these two rules are the *only* ways to
prove it.

Our machine `containsAB` looks for `ab` somewhere in the string. It has states
`s0`, `s1`, `s2`, and starts in `s0`.
"

/-- Reading nothing, `containsAB` can get from `s2` to `s2`. -/
Statement : containsAB.Path .s2 [] .s2 := by
  Hint "This is the first rule, `NFA.Path.nil`. Use `exact NFA.Path.nil _`:
  the `_` asks Lean to fill in the state itself."
  exact NFA.Path.nil _

Conclusion "
`_` is useful whenever Lean can work something out from the goal.
"

NewDefinition Automata.NFA Automata.NFA.Path Automata.NFA.Path.nil Automata.NFA.Path.cons
  Automata.containsAB Automata.ABState

end Automata
