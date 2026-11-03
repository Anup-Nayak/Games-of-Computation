import GameServer

/--
`rfl` proves a goal `X = Y` when both sides are equal *by computation*: Lean may
unfold definitions and evaluate while checking. It also proves `X ↔ X`.
-/
TacticDoc rfl

/--
`exact h` closes the goal with `h`, when `h` proves exactly the goal
(up to unfolding definitions). `h` can be an assumption or any expression,
like `h₂ h₁` or `⟨u, hu, v, hv, rfl⟩`.
-/
TacticDoc exact

/--
`rw [h]`, where `h : X = Y` (or `h : X ↔ Y`), replaces `X` by `Y` in the goal.

* `rw [h₁, h₂]` rewrites with several facts in turn.
* `rw [← h]` rewrites right-to-left.
* `rw [h] at h'` rewrites in the assumption `h'` instead of the goal.

After rewriting, `rw` tries to close the goal if both sides became identical.
-/
TacticDoc rw

/--
`intro x` introduces what the goal assumes:

* a goal `∀ x, P x` becomes `P x` for a new `x`;
* a goal `A → B` becomes `B` with a new assumption of `A`;
* a goal `L ⊆ M` takes a string `w` and `hw : w ∈ L`: use `intro w hw`;
* a goal `¬ P` becomes `False` with an assumption of `P`.
-/
TacticDoc intro

/-- `left` proves a goal `A ∨ B` by proving `A`. For languages: `w ∈ L ∪ M` by `w ∈ L`. -/
TacticDoc left

/-- `right` proves a goal `A ∨ B` by proving `B`. For languages: `w ∈ L ∪ M` by `w ∈ M`. -/
TacticDoc right

/--
`constructor` splits a goal into its parts:

* `A ∧ B` (and `w ∈ L ∩ M`) into `A` and `B`;
* `A ↔ B` into `A → B` and `B → A`.
-/
TacticDoc constructor

/--
`obtain` takes an assumption apart:

* `obtain ⟨h₁, h₂⟩ := h` for `h : A ∧ B`;
* `obtain ⟨x, hx⟩ := h` for `h : ∃ x, P x`, and longer patterns like
  `obtain ⟨u, hu, v, hv, hw⟩ := h` for nested ones;
* `obtain h | h := h` for `h : A ∨ B`, giving two cases.
-/
TacticDoc obtain

/--
`ext w` proves that two languages are equal by showing they contain the same
strings: the goal `L = M` becomes `w ∈ L ↔ w ∈ M`.
-/
TacticDoc ext

/--
`have` adds a new fact to your assumptions:

* `have h := e` names the expression `e`, for example `have h₁ := h [AB.a]`;
* `have h : P := by tac` proves `P` with tactics first.
-/
TacticDoc «have»

/--
`step` makes a machine read one symbol. It turns `M.evalFrom q (x :: xs)` into
`M.evalFrom q' xs`, working out the new state `q'` when it can, and turns
`M.evalFrom q []` into `q`.

`step` only sees a first symbol when the string visibly starts with one, like
`[AB.a, AB.b]` or `x :: xs`. Rewrite first if it doesn't.
-/
TacticDoc step

/--
`decide` answers a concrete yes-or-no question by computing, such as whether a
machine accepts a particular string. It can't prove statements about *every* string.
-/
TacticDoc decide

/--
`cases x` splits into one goal per possible shape of `x`: one per state of a
finite type like `Parity`, one per symbol of `AB`, or one per side of an *or*.
-/
TacticDoc cases

/--
`induction' n with n ih` proves a statement for every natural number `n`: first
for `0`, then for `n + 1` assuming it for `n` (the hypothesis `ih`).

For strings, `induction' w with x xs ih` gives a goal for the empty string and
one for `x :: xs`, assuming it for `xs`.

Add `generalizing q` at the end to make `ih` hold for every value of `q`. You
need this whenever `q` changes from one step to the next, like the state of a
machine.
-/
TacticDoc «induction'»

/--
`omega` proves arithmetic facts about natural numbers and integers: `+`, `-`,
numerals, multiplication by constants, `%` and `/` by constants, `<`, `≤`, `=`, `≠`.
It uses the arithmetic assumptions in your context.
-/
TacticDoc omega

/--
`by_cases h : P` splits the proof into two cases, one with `h : P` and one
with `h : ¬ P`.
-/
TacticDoc by_cases


/--
`exfalso` changes the goal into `False`. Use it when your assumptions
contradict each other: from a contradiction, anything follows.
-/
TacticDoc exfalso

/--
`apply h` works backwards from the goal. If `h` concludes the goal from some
assumptions, `apply h` leaves those assumptions as new goals.

You can fix some of `h`'s arguments by name, for example
`apply NFA.Path.cons (q := .s1)` to choose the next state of a path.
-/
TacticDoc apply

/--
`use x` proves a goal `∃ a, P a` by giving the witness `x`. You are left to prove `P x`.
-/
TacticDoc use

/--
`unfold d` replaces the definition `d` by its body in the goal, so that
theorems about what's inside can apply. For example `unfold DFA.inter` shows
that `M₁.inter M₂` is a product machine.
-/
TacticDoc unfold
