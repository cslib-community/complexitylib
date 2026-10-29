/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.BooleanAnalysis.HammingFourier
import Mathlib.Tactic.NormNum

/-! The noise distance between two distinct parities, which damps their disagreement by the size
of their sets; the relative Hamming distance of the constants; separation failing at `ρ = 0`; and
the metric `√D_ρ` at `ρ = 1`. -/

namespace ComplexityTests.CircuitHamming.Parseval

open Cslib Cslib.BitString Finset

/-! ### Parities -/

/-- Noise distance between distinct parities at `ρ = 1` (`1 / 2`) and `ρ = 1 / 2` (`5 / 64`), and
their relative Hamming distance read off the Fourier coefficients. -/
example :
    noiseDist 1 (parityOn ({0} : Finset (Fin 3))) (parityOn {1, 2}) = 1 / 2 ∧
      noiseDist (1 / 2) (parityOn ({0} : Finset (Fin 3))) (parityOn {1, 2}) = 5 / 64 ∧
      (hammingDist (parityOn ({0} : Finset (Fin 3))) (parityOn {1, 2}) : ℝ) / 2 ^ 3 = 1 / 2 := by
  refine ⟨by rw [noiseDist_parityOn 1 (by decide)]; norm_num,
    by rw [noiseDist_parityOn _ (by decide)]; norm_num, ?_⟩
  have h := noiseDist_one (parityOn ({0} : Finset (Fin 3))) (parityOn {1, 2})
  rw [noiseDist_parityOn 1 (by decide), Fintype.card_fin] at h
  rw [← h]
  norm_num

/-! ### The constants -/

/-- The two constants are at relative Hamming distance one, read off their Fourier
coefficients. -/
example : 1 / 4 * ∑ S : Finset (Fin 2), (fourierCoeff (fun _ => signVal false) S -
    fourierCoeff (fun _ => signVal true) S) ^ 2 = 1 := by
  rw [← hammingDist_div_eq_sum_fourierCoeff_sub_sq (fun _ : Fin 2 → Bool => false) fun _ => true]
  simp [hammingDist]
  norm_num

/-! ### Separation and the metric -/

/-- **Separation needs `ρ ≠ 0`**: at `ρ = 0` distinct parities have noise distance zero, whereas
at `ρ = 1 / 3` their noise distance is positive; `√D_1` is a metric and satisfies the triangle
inequality. -/
example (ρ : ℝ) :
    noiseDist 0 (parityOn ({0} : Finset (Fin 2))) (parityOn {1}) = 0 ∧
      parityOn ({0} : Finset (Fin 2)) ≠ parityOn {1} ∧
      0 < noiseDist (1 / 3) (parityOn ({0} : Finset (Fin 2))) (parityOn {1}) ∧
      (noiseMetricSpace (ι := Fin 2) one_ne_zero).dist (fun _ => false) (fun _ => true) = 1 ∧
      √(noiseDist ρ (parityOn ({0} : Finset (Fin 2))) (parityOn {1})) ≤
        √(noiseDist ρ (parityOn ({0} : Finset (Fin 2))) (parityOn {0, 1})) +
          √(noiseDist ρ (parityOn ({0, 1} : Finset (Fin 2))) (parityOn {1})) := by
  refine ⟨by rw [noiseDist_parityOn 0 (by decide)]; norm_num,
    fun h => absurd (congrFun h ![true, false]) (by decide),
    by rw [noiseDist_parityOn _ (by decide)]; norm_num,
    ?_,
    sqrt_noiseDist_triangle ρ _ _ _⟩
  have h : (hammingDist (fun _ : Fin 2 → Bool => false) fun _ => true : ℝ) / 2 ^ 2 = 1 := by
    simp [hammingDist]
    norm_num
  rw [noiseMetricSpace_dist, noiseDist_one, Fintype.card_fin, h, Real.sqrt_one]

end ComplexityTests.CircuitHamming.Parseval
