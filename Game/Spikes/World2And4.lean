import Game.Automata.Examples
import Mathlib.Tactic

/-! Spike: Worlds 2 and 4. Not imported by the game; a check that the definitions support these proofs. -/

namespace Automata
variable {α σ : Type}

/-! World 2 -/

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
      rw [DFA.mem_toNFA_step] at hq
      subst hq
      exact (ih _).1 hpath
    · intro h
      exact .cons rfl ((ih _).2 h)

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

example : [AB.b, .a, .b, .a] ∈ containsAB.accepts := by
  refine ⟨.s2, rfl, ?_⟩
  exact .cons (q := .s0) rfl
    (.cons (q := .s1) rfl
      (.cons (q := .s2) rfl
        (.cons (q := .s2) rfl (.nil _))))

/-! World 4: subset construction -/

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
