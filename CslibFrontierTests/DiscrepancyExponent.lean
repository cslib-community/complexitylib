/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module

import CslibFrontier.Computability.Communication.Lifting.LogarithmicLifting

/-! Regression clients for arbitrary positive discrepancy exponents and alphabet sizes. -/

open Cslib Cslib.Communication Cslib.Communication.Lifting Cslib.Probability

/-- The parameter choice is bounded and independent of the input dimension and alphabet. -/
example {η : ℝ} (hη : 0 < η) :
    ∃ k : ℕ, 1 ≤ k ∧ 1 ≤ 2 * (k : ℝ) * η ∧ (k : ℝ) ≤ 1 / (2 * η) + 1 :=
  exists_density_exponent_le hη

/-- Discrepancy exponent `1/100` is covered, unlike the previous fixed `1/2` endpoint.
The alphabet size is arbitrary subject to the lower bound, not a prescribed perfect power. -/
example {n m : ℕ} [NeZero m] (hn : 2 ≤ n) (hm : n ^ (2048 * 50 ^ 2) ≤ m)
    (g : Fin m → Fin m → Bool) (f : (Fin n → Bool) → Bool)
    (hd : discrepancy (PMF.uniformOfFintype (Fin m × Fin m)) g ≤
      (m : ℝ) ^ (-(1 / 100 : ℝ)))
    (p : Protocol (Fin n → Fin m) (Fin n → Fin m) Bool)
    (hp : ∀ x y, p.run x y = f (fun i => g (x i) (y i))) :
    ∃ t : DecisionTree (Fin n) Bool, (∀ z, t.eval z = f z) ∧
      (m : ℝ) ^ t.depth ≤ 8 ^ (256 * 50 * p.depth) :=
  exists_decisionTree_of_discrepancy_exponent (k := 50) (by norm_num) (by norm_num)
    hn hm g hd (fun z o => o = f z) p hp

/-- The real-root bridge also permits alphabets strictly between successive powers. -/
example {M : ℝ} (hM : (3 : ℝ) ^ 2048 ≤ M) :
    (3 : ℝ) ≤ M ^ ((2048 : ℝ)⁻¹) := by
  have hD : (0 : ℝ) ≤ M ^ (-(1 : ℝ)) :=
    Real.rpow_nonneg ((pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) 2048).trans hM) _
  have h := density_root_parameters (k := 1) (η := 1) (D := 0)
    (by norm_num) (by norm_num) (by norm_num : (2 : ℝ) ≤ 3) (by simpa using hM) hD
  simpa using h.2.1

#print axioms Cslib.Communication.Lifting.general_parameter_certificate
#print axioms Cslib.Communication.Lifting.density_root_parameters
#print axioms Cslib.Communication.Lifting.exists_decisionTree_of_discrepancy_exponent
#print axioms Cslib.Communication.Lifting.exists_general_lifting_parameter

#print axioms Cslib.Communication.Lifting.exists_decisionTree_logarithmic
