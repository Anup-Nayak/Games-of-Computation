import Game.Levels.NFA
import Game.Levels.Closure

World "Subset"
Level 1
Title "Tracking every guess"

namespace Automata

Introduction "
An NFA may be in several states at once, depending on its guesses. A DFA can't
guess, but it can **keep track of all the guesses**: let its states be *sets* of
NFA states.

This is the **subset construction**, `M.toDFA`:

* a state is a set `S` of states of `M`;
* reading `x` from `S` leads to every state reachable from some `p ∈ S` by
  one move: `{r | ∃ p ∈ S, r ∈ M.step p x}`;
* it starts in `{M.start}`;
* it accepts a set when the set contains an accepting state of `M`.

`M.toDFA` is a genuine DFA, with exactly one move each time. It just has a lot
of states: for an NFA with `n` states, the DFA has `2ⁿ`.
"

/-- `r ∈ M.toDFA.step S x ↔ ∃ p ∈ S, r ∈ M.step p x` -/
TheoremDoc Automata.NFA.mem_toDFA_step as "NFA.mem_toDFA_step" in "Subset"
TheoremTab "Subset"

/-- `r` is in the next set exactly when some state of `S` can move to `r`. -/
Statement NFA.mem_toDFA_step {α σ : Type} (M : NFA α σ) (S : Set σ) (x : α) (r : σ) :
    r ∈ M.toDFA.step S x ↔ ∃ p ∈ S, r ∈ M.step p x := by
  Hint "This is the definition of the move, so both sides are the same by `rfl`."
  rfl

NewDefinition Automata.NFA.toDFA

end Automata
