import GameServer
import Game.Automata.Examples

/-- `w ∈ M.accepts ↔ M.evalFrom M.start w ∈ M.accept` -/
TheoremDoc Automata.DFA.mem_accepts as "DFA.mem_accepts" in "DFA"

/-- `List.replicate (n + 1) a = a :: List.replicate n a` -/
TheoremDoc List.replicate_succ as "List.replicate_succ" in "Strings"

/-- `(a :: as) ++ bs = a :: (as ++ bs)` -/
TheoremDoc List.cons_append as "List.cons_append" in "Strings"

/-- `(a :: l).count a = l.count a + 1` -/
TheoremDoc List.count_cons_self as "List.count_cons_self" in "Strings"

/-- `b ≠ a → (b :: l).count a = l.count a` -/
TheoremDoc List.count_cons_of_ne as "List.count_cons_of_ne" in "Strings"

/-- `c → (if c then x else y) = x` -/
TheoremDoc if_pos as "if_pos" in "Logic"

/-- `¬ c → (if c then x else y) = y` -/
TheoremDoc if_neg as "if_neg" in "Logic"

/-- `w ∈ M.accepts ↔ ∃ f ∈ M.accept, M.Path M.start w f` -/
TheoremDoc Automata.NFA.mem_accepts as "NFA.mem_accepts" in "NFA"

/-- `q ∈ M.toNFA.step p x ↔ q = M.step p x` -/
TheoremDoc Automata.DFA.mem_toNFA_step as "DFA.mem_toNFA_step" in "NFA"

/-- `M.toNFA.start = M.start` -/
TheoremDoc Automata.DFA.toNFA_start as "DFA.toNFA_start" in "NFA"

/-- `w ∈ Lᶜ ↔ w ∉ L` -/
TheoremDoc Set.mem_compl_iff as "Set.mem_compl_iff" in "Languages"

/-- `w ∈ L₁ ∩ L₂ ↔ w ∈ L₁ ∧ w ∈ L₂` -/
TheoremDoc Set.mem_inter_iff as "Set.mem_inter_iff" in "Languages"

/-- `w ∈ L₁ ∪ L₂ ↔ w ∈ L₁ ∨ w ∈ L₂` -/
TheoremDoc Set.mem_union as "Set.mem_union" in "Languages"

/-- `M.compl.start = M.start` -/
TheoremDoc Automata.DFA.compl_start as "DFA.compl_start" in "Closure"

/-- `(M₁.prod M₂ acc).start = (M₁.start, M₂.start)` -/
TheoremDoc Automata.DFA.prod_start as "DFA.prod_start" in "Closure"

/-- `M.evalFrom q (x :: xs) = M.evalFrom (M.step q x) xs` -/
TheoremDoc Automata.DFA.evalFrom_cons as "DFA.evalFrom_cons" in "DFA"

/-- `M.toDFA.start = {M.start}` -/
TheoremDoc Automata.NFA.toDFA_start as "NFA.toDFA_start" in "Subset"

/-- `p ∈ {q} ↔ p = q` -/
TheoremDoc Set.mem_singleton_iff as "Set.mem_singleton_iff" in "Languages"

/-- `a ∈ {x | p x} = p a` -/
TheoremDoc Set.mem_setOf_eq as "Set.mem_setOf_eq" in "Languages"

/-- Pigeonhole: for `f : α → β` with `α` infinite and `β` finite,
`∃ i j, i ≠ j ∧ f i = f j`. -/
TheoremDoc Finite.exists_ne_map_eq_of_infinite as "Finite.exists_ne_map_eq_of_infinite" in "NonRegular"

/-- `(l₁ ++ l₂).count a = l₁.count a + l₂.count a` -/
TheoremDoc List.count_append as "List.count_append" in "Strings"

/-- `(List.replicate n a).count a = n` -/
TheoremDoc List.count_replicate_self as "List.count_replicate_self" in "Strings"

/-- `(List.replicate n b).count a = if b == a then n else 0` -/
TheoremDoc List.count_replicate as "List.count_replicate" in "Strings"

/-- `congrArg f : x = y → f x = f y` -/
TheoremDoc congrArg as "congrArg" in "Logic"
