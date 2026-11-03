import Game.Levels.DFA.L10_Parity

World "DFA"
Level 11
Title "The language of parityA"

namespace Automata

Introduction "
**Final level of this world.**

`parityA` accepts exactly the strings with an even number of `a`s.

Everything you need is already in your inventory: `ext`, `DFA.mem_accepts`,
`parityA_evalFrom`, `by_cases`, `if_pos` and `if_neg`. In one case you will need
to show a state is *not* accepting: remember the pattern from the
counterexample level, `have h₂ : ... ∉ ... := by decide`.

One new tactic: `exfalso` changes any goal into `False`. From a contradiction
you can prove anything, so when your assumptions contradict each other, use
`exfalso` and then derive `False`.
"

/-- `parityA.accepts = {w | w.count .a % 2 = 0}` -/
TheoremDoc Automata.parityA_accepts as "parityA_accepts" in "DFA"
TheoremTab "DFA"

/-- `parityA` accepts exactly the strings with an even number of `a`s. -/
Statement parityA_accepts : parityA.accepts = {w | w.count .a % 2 = 0} := by
  Hint "An equality of languages: start with `ext w`."
  ext w
  Hint "Unfold acceptance and use what you know about runs:
  `rw [DFA.mem_accepts, parityA_evalFrom]`."
  rw [DFA.mem_accepts, parityA_evalFrom]
  Hint "Everything depends on whether the count is even.
  `by_cases h : {w}.count AB.a % 2 = 0`."
  by_cases h : w.count .a % 2 = 0
  · Hint "The count is even, so the run ends in the start state: `rw [if_pos {h}]`."
    rw [if_pos h]
    Hint "Both sides are now true: the start state is accepting, and `{h}` says
    `{w}` is in the language. Prove the two directions with `constructor`."
    constructor
    · intro _
      exact h
    · intro _
      Hint "Is the start state accepting? That's true by computation."
      rfl
  · Hint "The count is odd, so the run ends in the flipped start state: `rw [if_neg {h}]`."
    rw [if_neg h]
    Hint "Now both sides are false. Prove the two directions with `constructor`."
    constructor
    · intro h'
      Hint "`{h'}` claims the flipped start state is accepting. That's false, and
      a concrete fact: `have h₂ : parityA.start.flip ∉ parityA.accept := by decide`."
      have h₂ : parityA.start.flip ∉ parityA.accept := by decide
      Hint "Your assumptions contradict each other, but the goal isn't `False`.
      Use `exfalso` first, then `exact {h₂} {h'}`."
      exfalso
      exact h₂ h'
    · intro h'
      Hint "`{h'}` says the count is even, and `{h}` says it isn't."
      exfalso
      exact h h'

Conclusion "
**World complete.** You proved that a machine recognises a language: the core
skill of this game. The recipe was:

1. describe the run from **every** state (induction, `generalizing`);
2. read off acceptance from the start state.

Next: machines that can guess.
"


NewTactic exfalso

end Automata
