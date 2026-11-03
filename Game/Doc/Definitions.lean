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

/--
A nondeterministic finite automaton over alphabet `α` with states `σ`:

* `M.step p x`: the **set** of states `M` may move to from `p` reading `x`
* `M.start`: the start state
* `M.accept`: the set of accepting states
-/
DefinitionDoc Automata.NFA as "NFA"

/--
`M.Path p w r`: reading `w`, `M` can get from `p` to `r`. Built by two rules:

* `NFA.Path.nil q : M.Path q [] q`
* `NFA.Path.cons : q ∈ M.step p x → M.Path q xs r → M.Path p (x :: xs) r`
-/
DefinitionDoc Automata.NFA.Path as "NFA.Path"

/-- `NFA.Path.nil q : M.Path q [] q`: reading nothing, you stay put. -/
DefinitionDoc Automata.NFA.Path.nil as "NFA.Path.nil"

/-- `NFA.Path.cons : q ∈ M.step p x → M.Path q xs r → M.Path p (x :: xs) r`:
one allowed move, then the rest of the path. -/
DefinitionDoc Automata.NFA.Path.cons as "NFA.Path.cons"

/-- The three states `s0`, `s1`, `s2` of `containsAB`. -/
DefinitionDoc Automata.ABState as "ABState"

/--
An NFA accepting the strings that contain `ab`. It starts in `s0` and accepts in `s2`.

| from | reading | may go to |
|---|---|---|
| `s0` | `a` | `s0` or `s1` |
| `s0` | `b` | `s0` |
| `s1` | `b` | `s2` |
| `s2` | `a` or `b` | `s2` |
-/
DefinitionDoc Automata.containsAB as "containsAB"

/-- `M.toNFA`: the DFA `M` as an NFA, with `M.toNFA.step p x = {M.step p x}`. -/
DefinitionDoc Automata.DFA.toNFA as "DFA.toNFA"

/-- `M.compl = { M with accept := M.acceptᶜ }`: the same machine, with accepting
and rejecting states swapped. -/
DefinitionDoc Automata.DFA.compl as "DFA.compl"

/--
`M₁.prod M₂ acc` runs `M₁` and `M₂` side by side on pairs of states:

* `(M₁.prod M₂ acc).step (p, q) x = (M₁.step p x, M₂.step q x)`
* start `(M₁.start, M₂.start)`, accepting states `acc`
-/
DefinitionDoc Automata.DFA.prod as "DFA.prod"

/-- `M₁.inter M₂`: the product accepting when both accept. -/
DefinitionDoc Automata.DFA.inter as "DFA.inter"

/-- `M₁.union M₂`: the product accepting when at least one accepts. -/
DefinitionDoc Automata.DFA.union as "DFA.union"

/-- `L.IsRegular`: some DFA with finitely many states recognises `L`.

`∃ (σ : Type) (_ : Finite σ) (M : DFA α σ), M.accepts = L` -/
DefinitionDoc Automata.Lang.IsRegular as "Lang.IsRegular"

/-- `inferInstance` asks Lean to find a standard fact by itself, such as
"a product of finite types is finite". -/
DefinitionDoc inferInstance as "inferInstance"
