/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.MaxCut.GoemansWilliamson
public import CslibFrontier.Computability.Complexity.Problems.MaxCut

/-!
# Goemans–Williamson rounding for the `MaxCut` problem

This module connects the Goemans–Williamson analysis in
`CslibFrontier.Algorithms.Lean.MaxCut.GoemansWilliamson` [GoemansWilliamson1995] to the weighted
maximum-cut problem `Cslib.Complexity.MaxCut`, whose edge lists have elements of type
`Cslib.Complexity.MaxCut.WeightedEdge` and whose cut weight is `Cslib.Complexity.MaxCut.cutWeight`.
Indexing the edges by their positions `Fin L.length`, `cutValue` is `cutWeight`
(`cutValue_eq_cutWeight`), and the guarantee for `ε`-optimal unit vectors restates for
`cutWeight`. Vertices are natural numbers; only the endpoints of `L` matter.

## Main results

* `Cslib.Algorithms.Lean.MaxCut.cutValue_eq_cutWeight`: `cutValue` on an edge list is
  `Cslib.Complexity.MaxCut.cutWeight`.
* `Cslib.Algorithms.Lean.MaxCut.goemansWilliamsonConstant_mul_cutWeight_le_integral`: the
  Goemans–Williamson guarantee for `Cslib.Complexity.MaxCut`.

## References

* [GoemansWilliamson1995]
-/

public section

open MeasureTheory ProbabilityTheory Real

namespace Cslib.Algorithms.Lean.MaxCut

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **`cutValue` is `MaxCut.cutWeight`.** On the edge list `L` of an instance of the weighted
`Cslib.Complexity.MaxCut` problem, indexed by positions, `cutValue` is the weight
`Cslib.Complexity.MaxCut.cutWeight L side`. -/
theorem cutValue_eq_cutWeight (L : List Cslib.Complexity.MaxCut.WeightedEdge) (side : ℕ → Bool) :
    cutValue (fun i : Fin L.length => (L[i].u, L[i].v)) (fun i => (L[i].weight : ℝ)) side =
      (Cslib.Complexity.MaxCut.cutWeight L side : ℝ) := by
  unfold cutValue
  simp only [Fin.getElem_fin]
  rw [Fin.sum_univ_fun_getElem L fun x => if side x.u ≠ side x.v then (x.weight : ℝ) else 0]
  unfold Cslib.Complexity.MaxCut.cutWeight
  induction L with
  | nil => simp
  | cons x L ih =>
    rw [List.map_cons, List.sum_cons, ih, List.filter_cons]
    by_cases h : side x.u = side x.v
    · simp [Cslib.Complexity.MaxCut.crosses, h]
    · simp [Cslib.Complexity.MaxCut.crosses, h]

variable [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] in
/-- **The Goemans–Williamson guarantee for `Cslib.Complexity.MaxCut`.** For the edge list `L` of
an instance of weighted MAX-CUT and unit vectors `v` within `ε` of optimal for its relaxation,
the expected weight of the rounded cut is at least `α` times the weight of every cut minus `ε`.
Vertices are natural numbers; only the endpoints of `L` matter. -/
theorem goemansWilliamsonConstant_mul_cutWeight_le_integral
    (L : List Cslib.Complexity.MaxCut.WeightedEdge)
    {v : ℕ → F} (hv : ∀ i, ‖v i‖ = 1) {ε : ℝ}
    (hopt : ∀ v' : ℕ → F, (∀ i, ‖v' i‖ = 1) →
      sdpValue (fun i : Fin L.length => (L[i].u, L[i].v)) (fun i => (L[i].weight : ℝ)) v' ≤
        sdpValue (fun i : Fin L.length => (L[i].u, L[i].v)) (fun i => (L[i].weight : ℝ)) v + ε)
    (side : ℕ → Bool) :
    goemansWilliamsonConstant * ((Cslib.Complexity.MaxCut.cutWeight L side : ℝ) - ε) ≤
      ∫ r, (Cslib.Complexity.MaxCut.cutWeight L (hyperplaneSide v r) : ℝ) ∂stdGaussian F := by
  simp only [← cutValue_eq_cutWeight]
  exact goemansWilliamsonConstant_mul_sub_le_integral _ (fun _ => Nat.cast_nonneg _) hv hopt side

end Cslib.Algorithms.Lean.MaxCut
