import Game.Levels.Subset.L08_Regular

World "Subset"
Level 9
Title "Putting it all together"

namespace Automata

Introduction "
**Final level of this world.** Is the language of strings that contain `ab`
*and* have an even number of `a`s regular?

You have every piece:

* `containsAB` is an NFA for the first condition, with finitely many states;
* `parityA` is a DFA for the second, with finitely many states;
* regular languages are closed under intersection.

For `parityA`, give the definition directly: `⟨Parity, inferInstance, parityA, rfl⟩`.
"

/-- Containing `ab` and an even number of `a`s is regular. -/
Statement : (containsAB.accepts ∩ parityA.accepts : Lang AB).IsRegular := by
  Hint "It's an intersection: `apply Lang.IsRegular.inter`."
  apply Lang.IsRegular.inter
  · Hint "`containsAB` is an NFA with finitely many states."
    exact NFA.accepts_isRegular containsAB
  · Hint "`parityA` itself is a DFA for this: `exact ⟨Parity, inferInstance, parityA, rfl⟩`."
    exact ⟨Parity, inferInstance, parityA, rfl⟩

Conclusion "
**World complete.** NFAs, DFAs, and the closure properties all fit together:
design each piece with whatever machine is easiest, and the theory guarantees
the combination is regular.

But are *all* languages regular? The last world answers that.
"

end Automata
