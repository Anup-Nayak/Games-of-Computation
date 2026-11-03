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
