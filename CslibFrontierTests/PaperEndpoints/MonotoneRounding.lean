/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Statistics.LeastSquares.Monotone

/-! Actual one-dimensional estimates and rounding with a nonsingular fixed observation. -/

open Cslib.LeastSquares Matrix

/-- A fixed unit observation with response zero, followed by an observation with response two. -/
public theorem scalar_estimate {a : ℝ} (ha : 0 ≤ a) :
    rankOneEstimate (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 (fun _ => 1) 2 a =
      fun _ => 2 * a / (1 + a) := by
  rw [rankOneEstimate_eq (by simpa using (PosDef.one :
    (1 : Matrix (Fin 1) (Fin 1) ℝ).PosDef)) _ _ _ ha]
  ext i
  simp only [inv_one, one_mulVec, mulVec_zero, dotProduct, Fin.sum_univ_succ,
    Fin.sum_univ_zero, mul_one, add_zero, Pi.add_apply, Pi.smul_apply,
    Pi.zero_apply, smul_eq_mul]
  ring

/-- The two endpoint estimates differ: rounding is not a vacuous constant experiment. -/
public theorem distinct_endpoints :
    rankOneEstimate (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 (fun _ => 1) 2 0 = 0 ∧
    rankOneEstimate (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 (fun _ => 1) 2 1 = 1 := by
  constructor
  · rw [scalar_estimate (by norm_num)]
    ext i
    norm_num
  · rw [scalar_estimate (by norm_num)]
    ext i
    norm_num

/-- Two fractional observations can be rounded while retaining the fixed positive Gram matrix. -/
public theorem two_observation_rounding :
    ∃ u : Fin 2 → ℝ, (∀ i, u i = 0 ∨ u i = 1) ∧
      (fun _ : Fin 1 => 1) ⬝ᵥ weightedEstimate 1 0 Finset.univ
        (fun _ _ => 1) (fun i : Fin 2 => if i = 0 then 2 else -1) u ≤
      (fun _ : Fin 1 => 1) ⬝ᵥ weightedEstimate 1 0 Finset.univ
        (fun _ _ => 1) (fun i : Fin 2 => if i = 0 then 2 else -1) (fun _ => 1 / 2) := by
  obtain ⟨u, hu, _, hcost⟩ := exists_round_weights
    (by simpa using (PosDef.one : (1 : Matrix (Fin 1) (Fin 1) ℝ).PosDef))
    0 (fun _ => 1) (Finset.univ : Finset (Fin 2)) (fun _ _ => 1)
    (fun i => if i = 0 then 2 else -1) (fun _ => 1 / 2) (by intro i hi; norm_num)
  exact ⟨u, fun i => hu i (Finset.mem_univ _), hcost⟩
