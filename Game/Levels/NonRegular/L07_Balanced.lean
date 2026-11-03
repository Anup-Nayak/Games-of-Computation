import Game.Levels.NonRegular.L06_Anbn

World "NonRegular"
Level 7
Title "Balanced strings"

namespace Automata

Introduction "
**Final level of the game.** The strings with as many `a`s as `b`s are not
regular either.

`balanced = {w | w.count .a = w.count .b}`

The same plan works, with the same strings: `aⁱbⁱ` is balanced, and `aʲbⁱ`
isn't. To unfold membership, `rw [balanced, Set.mem_setOf_eq]` turns
`w ∈ balanced` into `w.count .a = w.count .b`. Then your counting results do
the rest.
"

/-- No DFA recognises the strings with equally many `a`s and `b`s. -/
Statement : ¬ balanced.IsRegular := by
  intro h
  obtain ⟨σ, hσ, M, hM⟩ := h
  Hint (hidden := true) "Same start as last level: pigeonhole on powers of `a`."
  obtain ⟨i, j, hij, hcol⟩ := exists_collision M AB.a
  Hint "Show `aⁱbⁱ` is accepted. Inside the `have`, rewrite with `{hM}`, unfold
  `balanced`, and count:
  `rw [{hM}, balanced, Set.mem_setOf_eq, count_a_ab, count_b_ab]`."
  have hi : List.replicate i AB.a ++ List.replicate i AB.b ∈ M.accepts := by
    rw [hM, balanced, Set.mem_setOf_eq, count_a_ab, count_b_ab]
  have hj := (same_state_indist M hcol _).1 hi
  Hint "Do the same rewriting in `{hj}`. It then says `{j} = {i}`."
  rw [hM, balanced, Set.mem_setOf_eq, count_a_ab, count_b_ab] at hj
  omega

Conclusion "
**Game complete!**

You started with strings and lists. Along the way you have proved:

* exactly which language a DFA recognises;
* that NFAs recognise the same languages as DFAs, via the subset construction;
* that regular languages are closed under complement, intersection and union;
* that `aⁿbⁿ` and the balanced strings are **not** regular.

These are the core theorems of a first course on finite automata, and you proved
every one of them yourself, checked by Lean.
"

NewDefinition Automata.balanced
NewTheorem Set.mem_setOf_eq

end Automata
