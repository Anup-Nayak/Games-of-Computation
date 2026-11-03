import Game.Levels.Strings.L07_Ext

World "Strings"
Level 8
Title "Concatenation"

namespace Automata

Introduction "
The **concatenation** `L.concat M` contains every string that splits as a string
of `L` followed by a string of `M`:

`w ∈ L.concat M` means `∃ u ∈ L, ∃ v ∈ M, w = u ++ v`.

To prove a statement starting with `∃`, give the witness together with proofs
of the rest, bundled with angle brackets. Here the bundle is
`⟨u, proof u ∈ L, v, proof v ∈ M, proof w = u ++ v⟩`.

The language `{[AB.a]}` contains exactly one string, `a`.
"

/-- `ab` is in the concatenation of `{a}` and `{b}`. -/
Statement : [AB.a, .b] ∈ Lang.concat {[.a]} {[.b]} := by
  Hint "Which split works? Take `u = [AB.a]` and `v = [AB.b]`. Each of the three
  remaining facts is true by computation, so each proof is `rfl`.
  Try `exact ⟨[AB.a], rfl, [AB.b], rfl, rfl⟩`."
  exact ⟨[AB.a], rfl, [AB.b], rfl, rfl⟩

Conclusion "
The angle brackets build any *and* or *exists* at once, as long as you supply
all the pieces in order.
"

NewDefinition Automata.Lang.concat

end Automata
