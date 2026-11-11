/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.MaxTwoSAT.GoemansWilliamson
public import CslibFrontier.Computability.Complexity.Problems.MaxTwoSAT

/-!
# Goemans–Williamson rounding for the `MaxTwoSAT` problem

This module connects the Goemans–Williamson MAX-2SAT analysis in
`CslibFrontier.Algorithms.Lean.MaxTwoSAT.GoemansWilliamson` [GoemansWilliamson1995] to the
complexity-theoretic `Cslib.Complexity.MaxTwoSAT` problem on `CNF ℕ`, whose satisfied-clause count
is `φ.countP (Clause.eval σ)`. Indexing clauses by `Fin φ.length`, `satValue` equals
`(φ.countP (Clause.eval σ) : ℝ)` (`satValue_eq_countP`), and the `ε`-optimal rounding guarantee
restates directly for `MaxTwoSAT`.

## Main results

* `Cslib.Algorithms.Lean.MaxTwoSAT.satValue_eq_countP`: `satValue` with unit weights on a formula
  `φ : CNF V` is the number of satisfied clauses `(φ.countP (Clause.eval σ) : ℝ)`.
* `Cslib.Algorithms.Lean.MaxTwoSAT.goemansWilliamsonConstant_mul_countP_le_integral`: the
  Goemans–Williamson guarantee for `CNF.countP`.
* `Cslib.Algorithms.Lean.MaxTwoSAT.goemansWilliamsonConstant_mul_target_le_integral_of_mem`:
  for any `(φ, K) ∈ Cslib.Complexity.MaxTwoSAT` and `ε`-optimal unit vectors, the expected number
  of satisfied clauses under random-hyperplane rounding is at least `α ((K : ℝ) - ε)`.

## References

* [GoemansWilliamson1995]
-/

public section

open MeasureTheory ProbabilityTheory Real Cslib.Logic.PL

namespace Cslib.Algorithms.Lean.MaxTwoSAT

variable {V F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **`satValue` counts satisfied clauses.** For any `φ : CNF V` indexed by `Fin φ.length` with
unit weights, `satValue` is `(φ.countP (Clause.eval σ) : ℝ)`. -/
theorem satValue_eq_countP (φ : CNF V) (σ : V → Bool) :
    satValue (fun i : Fin φ.length => φ[i]) (fun _ => 1) σ =
      (φ.countP (Clause.eval σ) : ℝ) := by
  unfold satValue
  simp only [Fin.getElem_fin]
  rw [Fin.sum_univ_fun_getElem φ fun c => if c.eval σ = true then (1 : ℝ) else 0]
  induction φ with
  | nil => simp
  | cons c φ ih =>
    rw [List.map_cons, List.sum_cons, ih, List.countP_cons]
    by_cases h : c.eval σ = true
    · simp [h, add_comm]
    · simp [h]

variable [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

/-- **Goemans–Williamson guarantee for `CNF.countP`.** Given `φ : CNF V` with all clauses of length
at most `2` and `ε`-optimal unit vectors `v : Option V → F`, the expected satisfied-clause count is
at least `α ((φ.countP (Clause.eval σ) : ℝ) - ε)` for every assignment `σ`. -/
theorem goemansWilliamsonConstant_mul_countP_le_integral (φ : CNF V) (hφ : ∀ c ∈ φ, c.length ≤ 2)
    {v : Option V → F} (hv : ∀ o, ‖v o‖ = 1) {ε : ℝ}
    (hopt : ∀ v' : Option V → F, (∀ o, ‖v' o‖ = 1) →
      satSdpValue (fun i : Fin φ.length => φ[i]) (fun _ => 1) v' ≤
        satSdpValue (fun i : Fin φ.length => φ[i]) (fun _ => 1) v + ε)
    (σ : V → Bool) :
    goemansWilliamsonConstant * ((φ.countP (Clause.eval σ) : ℝ) - ε) ≤
      ∫ r, (φ.countP (Clause.eval (satHyperplaneAssignment v r)) : ℝ) ∂stdGaussian F := by
  simp only [← satValue_eq_countP]
  exact goemansWilliamsonConstant_mul_sub_le_integral (fun i : Fin φ.length => φ[i])
    (fun i => hφ φ[i] (List.getElem_mem i.2)) (fun _ => zero_le_one) hv hopt σ

/-- **Goemans–Williamson guarantee for `Cslib.Complexity.MaxTwoSAT`.** If `(φ, K) ∈ MaxTwoSAT` and
unit vectors `v` are within `ε` of optimal for `satSdpValue`, then the expected number of clauses
satisfied by `satHyperplaneAssignment v r` is at least `α ((K : ℝ) - ε)`. -/
theorem goemansWilliamsonConstant_mul_target_le_integral_of_mem {φ : CNF ℕ} {K : ℕ}
    (hmem : (φ, K) ∈ Cslib.Complexity.MaxTwoSAT) {v : Option ℕ → F} (hv : ∀ o, ‖v o‖ = 1)
    {ε : ℝ} (hopt : ∀ v' : Option ℕ → F, (∀ o, ‖v' o‖ = 1) →
      satSdpValue (fun i : Fin φ.length => φ[i]) (fun _ => 1) v' ≤
        satSdpValue (fun i : Fin φ.length => φ[i]) (fun _ => 1) v + ε) :
    goemansWilliamsonConstant * ((K : ℝ) - ε) ≤
      ∫ r, (φ.countP (Clause.eval (satHyperplaneAssignment v r)) : ℝ) ∂stdGaussian F := by
  obtain ⟨h2, σ, hK⟩ := Cslib.Complexity.mem_MaxTwoSAT_iff.1 hmem
  have hK' : (K : ℝ) ≤ (φ.countP (Clause.eval σ) : ℝ) := by exact_mod_cast hK
  have h1 := mul_le_mul_of_nonneg_left (sub_le_sub_right hK' ε) goemansWilliamsonConstant_nonneg
  exact h1.trans (goemansWilliamsonConstant_mul_countP_le_integral φ h2 hv hopt σ)

end Cslib.Algorithms.Lean.MaxTwoSAT
