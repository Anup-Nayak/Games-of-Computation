import GameServer
import Game.Automata.Examples

/-- The alphabet `{a, b}`, with symbols `AB.a` and `AB.b` (or `.a` and `.b` when the type is clear). -/
DefinitionDoc Automata.AB as "AB"

/-- The symbol `a` of the alphabet `AB`. -/
DefinitionDoc Automata.AB.a as "AB.a"

/-- The symbol `b` of the alphabet `AB`. -/
DefinitionDoc Automata.AB.b as "AB.b"

/--
`Lang α` is the type of languages over the alphabet `α`: sets of strings.

* `w ∈ L`: `w` is in `L`
* `L ∪ M`, `L ∩ M`: union, intersection
* `L ⊆ M`: every string of `L` is in `M`
* `{w | P w}`: the strings with property `P`
-/
DefinitionDoc Automata.Lang as "Lang"

/--
`L.concat M` contains every string that splits as a string of `L` followed by a
string of `M`:

`w ∈ L.concat M ↔ ∃ u ∈ L, ∃ v ∈ M, w = u ++ v`
-/
DefinitionDoc Automata.Lang.concat as "Lang.concat"

/--
A deterministic finite automaton over alphabet `α` with states `σ`:

* `M.step q x`: the next state after reading `x` in state `q`
* `M.start`: the start state
* `M.accept`: the set of accepting states
-/
DefinitionDoc Automata.DFA as "DFA"

/--
`M.evalFrom q w` is the state `M` is in after reading `w`, starting in `q`:

* `M.evalFrom q [] = q`
* `M.evalFrom q (x :: xs) = M.evalFrom (M.step q x) xs`
-/
DefinitionDoc Automata.DFA.evalFrom as "evalFrom"

/--
`M.accepts` is the language of `M`: the strings whose run from `M.start`
ends in an accepting state.
-/
DefinitionDoc Automata.DFA.accepts as "accepts"

/-- The two states `Parity.even` and `Parity.odd`. -/
DefinitionDoc Automata.Parity as "Parity"

/-- `q.flip` swaps the two states: `even.flip = odd`, `odd.flip = even`. -/
DefinitionDoc Automata.Parity.flip as "Parity.flip"

/--
`parityA` has states `even` and `odd`. Reading `a` swaps them, reading `b`
changes nothing. It starts in `even` and accepts in `even`.
-/
DefinitionDoc Automata.parityA as "parityA"
