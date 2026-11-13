/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.MachineLearning.Rademacher.Chaining
import CslibFrontier.Probability.PMF.ToReal
import CslibFrontierTests.RealizablePAC

/-! Checks for the chaining bound on the Rademacher complexity of VC classes. For thresholds on
`ℕ`, which shatter no two points, the empirical complexity on `m` points is at most `32 / √m` for
every `m`, with no factor `log m`. For all binary classifiers on `Bool` (`d = 2`), `2 ^ 20` examples
make an empirical risk minimizer `0.05`-optimal with probability `19 / 20`. The logarithmic VC bound
has a smaller constant at these sizes; the chaining bound has the better rate. -/

namespace CslibFrontierTests.RademacherChaining

open Cslib.MachineLearning Cslib.MachineLearning.PACLearning
open CslibFrontierTests.RealizablePAC (thresholds card_le_one_of_setShatters_thresholds)

/-- The empirical Rademacher complexity of thresholds on any `m` points is at most `32 / √m`. -/
example {m : ℕ} (S : Fin m → ℕ) :
    empiricalRademacherComplexity (signClass thresholds) S ≤ 32 / √m := by
  have h := empiricalRademacherComplexity_signClass_le_mul_sqrt
    (fun _ hW => card_le_one_of_setShatters_thresholds hW) S
  rwa [Nat.cast_one, Real.sqrt_div' _ (Nat.cast_nonneg m), Real.sqrt_one, mul_one_div] at h

/-- On `4 ^ 10 = 2 ^ 20` points, the empirical Rademacher complexity of thresholds is at most
`1 / 32`. -/
example (S : Fin (4 ^ 10) → ℕ) :
    empiricalRademacherComplexity (signClass thresholds) S ≤ 1 / 32 := by
  refine (empiricalRademacherComplexity_signClass_le_mul_sqrt
    (fun _ hW => card_le_one_of_setShatters_thresholds hW) S).trans_eq ?_
  rw [show ((1 : ℕ) : ℝ) / ((4 ^ 10 : ℕ) : ℝ) = (1 / 1024) ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]
  norm_num

/-- Agnostic learning by ERM with `d = 2`, `m = 2 ^ 20` and `δ = 1 / 20`: with probability at least
`19 / 20`, an empirical risk minimizer over all binary classifiers on `Bool` has true error within
`0.05` of every classifier. -/
example (D : PMF (Bool × Bool)) {A : Learner Bool Bool (2 ^ 20)} (hA : IsERM A Set.univ) :
    ((Cslib.Probability.PMF.pi fun _ : Fin (2 ^ 20) => D).toOuterMeasure
      {S | ∃ c : Bool → Bool, (D.toOuterMeasure {p | c p.1 ≠ p.2}).toReal + 5 / 100 <
        (D.toOuterMeasure {p | A S p.1 ≠ p.2}).toReal}).toReal ≤ 1 / 20 := by
  have hvc : 32 * √(((2 : ℕ) : ℝ) / ((2 ^ 20 : ℕ) : ℝ)) ≤ 45 / 1000 := by
    have : √(((2 : ℕ) : ℝ) / ((2 ^ 20 : ℕ) : ℝ)) ≤ 45 / 32000 :=
      (Real.sqrt_le_left (by norm_num)).2 (by norm_num)
    linarith
  have hδ : √(2 * Real.log (2 / (1 / 20)) / ((2 ^ 20 : ℕ) : ℝ)) ≤ 5 / 1000 := by
    have hlog : Real.log (2 / (1 / 20)) ≤ 4 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have he := Real.exp_one_gt_d9
      calc (2 / (1 / 20) : ℝ) ≤ (27 / 10) ^ 4 := by norm_num
        _ ≤ Real.exp 1 ^ 4 := by gcongr; linarith
        _ = Real.exp 4 := by rw [← Real.exp_nat_mul]; norm_num
    refine (Real.sqrt_le_left (by norm_num)).2 ?_
    push_cast
    linarith
  refine le_trans (Cslib.Probability.PMF.toOuterMeasure_toReal_mono _ ?_)
    (hA.vc_agnostic_bound_mul_sqrt D (d := 2) (fun W _ => by simpa using W.card_le_univ)
      (by norm_num) (by norm_num : (0 : ℝ) < 1 / 20))
  rintro S ⟨c, hlt⟩
  refine ⟨c, Set.mem_univ c, ?_⟩
  linarith

end CslibFrontierTests.RademacherChaining
