import Game.Levels.Strings.L08_Concat

World "Strings"
Level 9
Title "Concatenation distributes over union"

namespace Automata

Introduction "
**Final level of this world.**

Splitting `w` as `u ++ v` with `v ∈ M ∪ N` means `v ∈ M` or `v ∈ N`. So the
strings of `L.concat (M ∪ N)` are exactly those of `L.concat M` together with
those of `L.concat N`.

You have every tool you need: `ext`, `constructor`, `intro`, `obtain`, `left`,
`right`, and the angle brackets. Note that `obtain` can take apart an `∃` too:
`obtain ⟨u, hu, v, hv, hw⟩ := h`.
"

/-- `L.concat (M ∪ N) = L.concat M ∪ L.concat N` -/
TheoremDoc Automata.Lang.concat_union as "Lang.concat_union" in "Languages"
TheoremTab "Languages"

/-- Concatenation distributes over union. -/
Statement Lang.concat_union (L M N : Lang AB) :
    L.concat (M ∪ N) = L.concat M ∪ L.concat N := by
  Hint "As always for an equality of languages, start with `ext w` and `constructor`."
  ext w
  constructor
  · intro h
    Hint "Take `{h}` apart into its pieces with `obtain ⟨u, hu, v, hv, hw⟩ := {h}`."
    obtain ⟨u, hu, v, hv, hw⟩ := h
    Hint "`{hv}` is an *or*. Which language `{v}` is in decides which side of
    the goal you prove. Split it with `obtain hv | hv := {hv}`."
    obtain hv | hv := hv
    · Hint (hidden := true) "Here `{v} ∈ {M}`, so prove the left side, then give
      the same split: `exact ⟨{u}, {hu}, {v}, {hv}, {hw}⟩`."
      left
      exact ⟨u, hu, v, hv, hw⟩
    · right
      exact ⟨u, hu, v, hv, hw⟩
  · intro h
    Hint "Now the *or* comes first. Split `{h}` into its two cases."
    obtain h | h := h
    · obtain ⟨u, hu, v, hv, hw⟩ := h
      Hint "You need `{v} ∈ {M} ∪ {N}`, which is itself an *or*. Inside angle
      brackets, you can't use `left`, but you can prove it separately first:
      `have hv' : {v} ∈ {M} ∪ {N} := by left; exact {hv}`."
      have hv' : v ∈ M ∪ N := by
        left
        exact hv
      exact ⟨u, hu, v, hv', hw⟩
    · obtain ⟨u, hu, v, hv, hw⟩ := h
      have hv' : v ∈ M ∪ N := by
        right
        exact hv
      exact ⟨u, hu, v, hv', hw⟩

Conclusion "
**World complete.** You can now reason about strings and languages: membership,
union, intersection, equality and concatenation.

Next: machines that *recognise* languages.
"

NewTactic «have»

end Automata
