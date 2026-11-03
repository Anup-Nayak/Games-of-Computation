import GameServer

/--
`rfl` closes a goal of the form `A = A`, where both sides are equal
*by definition*. Lean is allowed to unfold definitions and compute while
checking this, so `rfl` can prove that a machine ends in a particular state
after reading a short, concrete string.
-/
TacticDoc rfl
