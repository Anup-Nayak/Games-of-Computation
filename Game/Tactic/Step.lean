import Game.Tactic.StepAttr
import Game.Automata.Defs

/-- `step` reads one symbol: it turns `M.evalFrom q (x :: xs)` into
`M.evalFrom q' xs` with the new state `q'` worked out, and
`M.evalFrom q []` into `q`. -/
macro "step" : tactic => `(tactic| (first
  | (rw [Automata.DFA.evalFrom_cons]; try simp only [step_simp])
  | rw [Automata.DFA.evalFrom_nil]
  | fail "`step` needs a run `evalFrom q w` where the string `w` is visibly empty or starts with a symbol"))
