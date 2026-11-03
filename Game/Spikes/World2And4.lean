import Game.Automata.Examples
import Mathlib.Tactic

/-! Spike: Worlds 2 and 4. Not imported by the game; a check that the definitions support these proofs. -/

namespace Automata
variable {α σ : Type}

/-! World 2 -/

def DFA.toNFA (M : DFA α σ) : NFA α σ where
  step q x := {M.step q x}
  start := M.start
  accept := M.accept

@[simp] theorem DFA.toNFA_step (M : DFA α σ) (q : σ) (x : α) :
    M.toNFA.step q x = {M.step q x} := rfl
@[simp] theorem DFA.toNFA_start (M : DFA α σ) : M.toNFA.start = M.start := rfl
@[simp] theorem DFA.toNFA_accept (M : DFA α σ) : M.toNFA.accept = M.accept := rfl

theorem DFA.toNFA_path (M : DFA α σ) (p r : σ) (w : List α) :
    M.toNFA.Path p w r ↔ M.evalFrom p w = r := by
  induction w generalizing p with
  | nil =>
    constructor
    · rintro ⟨⟩; rfl
    · rintro rfl; exact .nil _
  | cons x xs ih =>
    constructor
    · rintro (_ | ⟨hq, hpath⟩)
      rw [DFA.toNFA_step, Set.mem_singleton_iff] at hq
      subst hq
      exact (ih _).1 hpath
    · intro h
      exact .cons (by simp) ((ih _).2 h)

theorem DFA.toNFA_accepts (M : DFA α σ) : M.toNFA.accepts = M.accepts := by
  ext w
  constructor
  · rintro ⟨f, hf, hp⟩
    rw [DFA.toNFA_start, DFA.toNFA_path] at hp
    rw [DFA.toNFA_accept] at hf
    show M.evalFrom M.start w ∈ M.accept
    rw [hp]; exact hf
  · intro h
    exact ⟨_, h, (M.toNFA_path _ _ _).2 rfl⟩

/-- Strings containing `ab`: guess where it starts. -/
inductive ABState | s0 | s1 | s2
  deriving DecidableEq, Repr

def containsAB : NFA AB ABState where
  step q x := match q, x with
    | .s0, _  => if x = .a then {.s0, .s1} else {.s0}
    | .s1, .b => {.s2}
    | .s1, .a => ∅
    | .s2, _  => {.s2}
  start := .s0
  accept := {.s2}

example : [AB.b, .a, .b, .a] ∈ containsAB.accepts := by
  refine ⟨.s2, rfl, ?_⟩
  exact .cons (q := .s0) (by simp [containsAB])
    (.cons (q := .s1) (by simp [containsAB])
      (.cons (q := .s2) (by simp [containsAB])
        (.cons (q := .s2) (by simp [containsAB]) (.nil _))))

/-! World 4: subset construction -/

def NFA.toDFA (M : NFA α σ) : DFA α (Set σ) where
  step S x := {r | ∃ p ∈ S, r ∈ M.step p x}
  start := {M.start}
  accept := {S | ∃ q ∈ S, q ∈ M.accept}

/-- The strengthened statement: works for every starting set `S`. -/
theorem NFA.toDFA_evalFrom (M : NFA α σ) (S : Set σ) (w : List α) :
    M.toDFA.evalFrom S w = {r | ∃ p ∈ S, M.Path p w r} := by
  induction w generalizing S with
  | nil =>
    ext r
    constructor
    · intro h; exact ⟨r, h, .nil r⟩
    · rintro ⟨p, hp, ⟨⟩⟩; exact hp
  | cons x xs ih =>
    rw [DFA.evalFrom_cons, ih]
    ext r
    constructor
    · rintro ⟨q, ⟨p, hp, hq⟩, hpath⟩
      exact ⟨p, hp, .cons hq hpath⟩
    · rintro ⟨p, hp, (_ | ⟨hq, hpath⟩)⟩
      exact ⟨_, ⟨p, hp, hq⟩, hpath⟩

theorem NFA.toDFA_accepts (M : NFA α σ) : M.toDFA.accepts = M.accepts := by
  ext w
  constructor
  · rintro ⟨f, hf, hacc⟩
    have : f ∈ M.toDFA.evalFrom {M.start} w := hf
    rw [NFA.toDFA_evalFrom] at this
    obtain ⟨p, rfl, hp⟩ := this
    exact ⟨f, hacc, hp⟩
  · rintro ⟨f, hf, hp⟩
    refine ⟨f, ?_, hf⟩
    show f ∈ M.toDFA.evalFrom {M.start} w
    rw [NFA.toDFA_evalFrom]
    exact ⟨M.start, rfl, hp⟩

/-- Every NFA language with finitely many states is regular. -/
theorem NFA.accepts_isRegular [Finite σ] (M : NFA α σ) : M.accepts.IsRegular :=
  ⟨Set σ, inferInstance, M.toDFA, M.toDFA_accepts⟩

end Automata
