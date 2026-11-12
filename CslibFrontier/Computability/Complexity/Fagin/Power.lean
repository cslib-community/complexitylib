/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Fagin.Small
public import CslibFrontier.Logics.FirstOrder.Encoding.Power

/-!
# ESO definability through the power language

Pulling an existential second-order sentence over `v.powerLanguage` back along the power
interpretation `v.powerInterpretation k har` (`CslibFrontier/Logics/FirstOrder/Encoding/Power.lean`)
and existentially quantifying the linear order reduces existential second-order definability of an
isomorphism-closed class `K` over `L` to constructing an existential second-order sentence over
`v.powerLanguage` on the numeric structures `Fin (a.1 ^ k)` for well-formed inputs `a` with
`2 ≤ a.1`. Cardinalities `0` and `1` are handled by `ESO.Definable.of_withLinearOrder_card_ge_two`
(`CslibFrontier/Computability/Complexity/Fagin/Small.lean`).

## Main results

* `Cslib.Logic.ESO.Definable.of_powerLanguage`: reduces `ESO.Definable K` to an `ESO.Sentence`
  over `v.powerLanguage` on `Fin (a.1 ^ k)` for well-formed inputs `a` with `2 ≤ a.1`.

## References

* [R. Fagin, *Generalized first-order spectra and polynomial-time recognizable sets*][Fagin1974]
* [N. Immerman, *Descriptive Complexity*][Immerman1999]
-/

public section

universe u v

open FirstOrder Language CategoryTheory

namespace Cslib.Logic

namespace ESO

variable {L : Language.{u, v}} [L.IsRelational]

/-- To prove that an isomorphism-closed class `K` over a finite relational vocabulary `v` is
existential second-order definable, it suffices to choose a tuple width `k ≥ 1` bounding all
arities of `v` and an existential second-order sentence `Ψ : ESO.Sentence v.powerLanguage` that
agrees with `v.queryLanguage K` on the numeric structures `Fin (a.1 ^ k)` for all well-formed
inputs `a` with `2 ≤ a.1`. -/
theorem Definable.of_powerLanguage (v : Vocabulary L) {K : Set (Bundled.{0} L.Structure)}
    (hK : IsoClosed K) (k : ℕ) (hk : 1 ≤ k) (har : ∀ i : Fin v.count, v.arity i ≤ k)
    (Ψ : Sentence v.powerLanguage)
    (hΨ : ∀ a : EncodedStructure, v.WellFormed a → 2 ≤ a.1 →
      (a ∈ v.queryLanguage K ↔
        letI := v.powerStructure a (a.1 ^ k)
        Ψ.Realize (Fin (a.1 ^ k)))) :
    Definable K := by
  refine Definable.of_withLinearOrder_card_ge_two v hK
    ((v.powerInterpretation k har).onESOSentence Ψ) fun M _ e h2 => ?_
  rw [v.realize_onESOSentence_powerInterpretation k hk har M e Ψ]
  have hΨ' := hΨ (v.encode M e) (v.wellFormed_encode M e) h2
  rw [v.mem_queryLanguage_encode hK M e] at hΨ'
  exact hΨ'

end ESO

end Cslib.Logic
