/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Probability.RejectionSampling

/-! Exact box sampling laws, independent of the protocol client. -/

namespace CslibFrontierTests.RejectionSampling

open Cslib.Probability Cslib.Probability.PMF
open scoped ENNReal

/-! ### Box rejection sampling

In one dimension with `γ = 2` and `β = 1`, every shift in `[-1, 1]` gives the same law: accept
with probability `3 / 5`, uniformly on `[-1, 1]`. -/

example : boxReject (Fin 1) 2 1 ![1] = boxReject (Fin 1) 2 1 ![-1] :=
  boxReject_eq (by norm_num) (by decide) (by decide)

example : boxReject (Fin 1) 2 1 ![1] none = 1 - (3 / 5) ^ 1 := by
  rw [boxReject_apply_none (by norm_num) (by decide)]
  norm_num

example : boxReject (Fin 1) 2 1 ![1] none ≤ 2 / 5 := by
  have h := boxReject_apply_none_le (ι := Fin 1) (γ := 2) (β := 1) (v := ![1]) (by norm_num)
    (by decide)
  norm_num at h
  exact h

/-- The accepted value `1` has probability `1 / 5`, though `1 - 1 = 0` is the only draw that
produces it. -/
example : boxReject (Fin 1) 2 1 ![1] (some ![1]) = 5⁻¹ := by
  rw [boxReject, shiftReject_apply_some (fun _ hz => sub_mem_intBox (by norm_num) hz
    (by decide)), card_intBox]
  simp only [Fintype.card_fin, pow_one]
  rw [ite_eq_left (by decide)]
  norm_num

-- Empty dimension has exactly one accepted point.
example : boxReject (Fin 0) 0 0 0 none = 0 := by
  rw [boxReject_apply_none (by omega) (by simp)]
  simp

-- A singleton outer and inner box never aborts.
example : boxReject (Fin 1) 0 0 0 none = 0 := by
  rw [boxReject_apply_none (by omega) (by simp)]
  norm_num

end CslibFrontierTests.RejectionSampling
