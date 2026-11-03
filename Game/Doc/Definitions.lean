import GameServer
import Game.Automata.Examples

/--
`M.evalFrom q w` is the state the machine `M` is in after reading the
string `w`, starting from state `q`. It reads one symbol at a time:

* `M.evalFrom q [] = q`
* `M.evalFrom q (x :: xs) = M.evalFrom (M.step q x) xs`
-/
DefinitionDoc Automata.DFA.evalFrom as "evalFrom"

/--
`parityA` has two states, `even` and `odd`. Reading `a` swaps them,
reading `b` leaves the state alone. It starts in `even` and accepts in `even`.
-/
DefinitionDoc Automata.parityA as "parityA"
