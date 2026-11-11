/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.MatrixMultiplication.Schonhage.BoxTradeoff
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Explicit natural thresholds and a rational finite saving

The source's switch `ceil(m/9)` is computed by the natural expression `(m+8)/9`.
At the block parameters `m=9k`, `L=189k`, it is exactly `k`. Both the retained boxes
and all query occurrences then have a common rational decay factor `(9/20)^k`.
The query estimate needs the occurrence sparsity bound `Q*2^m ≤ N²`, so duplicates
remain charged. The table estimate needs one band to fit the original dimension.

These are finite specializations of the estimates in `BoxTradeoff`, at the parameters
used by [AlmanWilliams2026, Corollary 26]. Restricting to multiples of nine makes this
finite saving algebraic; it is an original specialization of the primary proof rather
than its full analytic corollary. No total encoding/preprocessing bound or final
algorithmic exponent is asserted here.
-/

public section

namespace Cslib.Algorithms.MatrixMultiplication.Schonhage.BoxTradeoff

open Finset

/-- An executable natural expression for the source's switching order `ceil(m/9)`. -/
@[expose] def ninthThreshold (m : ℕ) : ℕ := (m + 8) / 9

/-- The executable threshold is within the valid original order range, including `m=0`. -/
theorem ninthThreshold_le (m : ℕ) : ninthThreshold m ≤ m := by
  unfold ninthThreshold
  omega

/-- Nine times the rounded-up threshold covers the original inner depth. -/
theorem le_nine_mul_ninthThreshold (m : ℕ) : m ≤ 9 * ninthThreshold m := by
  unfold ninthThreshold
  omega

/-- The natural expression rounds up by fewer than nine units. -/
theorem nine_mul_ninthThreshold_lt (m : ℕ) : 9 * ninthThreshold m < m + 9 := by
  unfold ninthThreshold
  omega

@[simp] theorem ninthThreshold_nine_mul (k : ℕ) : ninthThreshold (9 * k) = k := by
  unfold ninthThreshold
  omega

/-- At block parameters, the per-query finite count has an explicit rational exponential base. -/
theorem sum_alpha_ninth_blocks (k : ℕ) :
    ∑ d ∈ range (k + 1), (alpha (9 * k) d : ℝ) ≤
      ((72 : ℝ) * (9 / 8 : ℝ) ^ 9) ^ k := by
  have h := sum_alpha_le_seventytwo (m := 9 * k) (t := k) (by omega)
  simpa only [pow_mul, mul_pow] using h

/-- Under the original-occurrence sparsity bound, all sparse query terms share the
same rational decay factor as the retained-box estimates. No query count is assumed free. -/
theorem queries_ninth_blocks (k N Q : ℕ) (hQ : Q * 2 ^ (9 * k) ≤ N ^ 2) :
    (Q : ℝ) * (∑ d ∈ range (k + 1), (alpha (9 * k) d : ℝ)) ≤
      (9 / 20 : ℝ) ^ k * (N : ℝ) ^ 2 := by
  have hQr : (Q : ℝ) * (2 : ℝ) ^ (9 * k) ≤ (N : ℝ) ^ 2 := by exact_mod_cast hQ
  have he : ((72 : ℝ) * (9 / 8 : ℝ) ^ 9) ^ k =
      ((72 : ℝ) * (9 / 16 : ℝ) ^ 9) ^ k * (2 : ℝ) ^ (9 * k) := by
    rw [pow_mul, ← mul_pow]
    congr 1
    norm_num
  have hbase : (72 : ℝ) * (9 / 16 : ℝ) ^ 9 ≤ 9 / 20 := by norm_num
  calc (Q : ℝ) * (∑ d ∈ range (k + 1), (alpha (9 * k) d : ℝ))
      ≤ (Q : ℝ) * (((72 : ℝ) * (9 / 8 : ℝ) ^ 9) ^ k) :=
        mul_le_mul_of_nonneg_left (sum_alpha_ninth_blocks k) (Nat.cast_nonneg _)
    _ = ((Q : ℝ) * (2 : ℝ) ^ (9 * k)) *
        (((72 : ℝ) * (9 / 16 : ℝ) ^ 9) ^ k) := by rw [he]; ring
    _ ≤ (N : ℝ) ^ 2 * (((72 : ℝ) * (9 / 16 : ℝ) ^ 9) ^ k) := by gcongr
    _ ≤ (N : ℝ) ^ 2 * (9 / 20 : ℝ) ^ k := by gcongr
    _ = _ := by ring

/-- The all-tile retained-value count has the same rational decay at the block parameters.
Its explicit band-size premise is weaker than an assumed asymptotic execution bound. -/
theorem boxes_ninth_blocks (k N : ℕ)
    (hN : K0 (189 * k) (9 * k) * N0 (189 * k) (9 * k) ≤ N) :
    ((tiles (189 * k) (9 * k) N).card : ℝ) *
        ((boxes (189 * k) (9 * k) k).card : ℝ) ≤
      32 * ((9 * k : ℕ) + 1 : ℝ) * (9 / 20 : ℝ) ^ k * (N : ℝ) ^ 2 := by
  have heq : 189 * k = 21 * (9 * k) := by omega
  obtain ⟨hrho, hfactor⟩ := rho_twentyone (9 * k)
  have hpow : rho (21 * (9 * k)) (9 * k) ^ k ≤ (9 / 20 : ℝ) ^ k :=
    pow_le_pow_left₀ (rho_nonneg (by omega)) hrho.le _
  have hdecay : rho (189 * k) (9 * k) ^ k / (1 - rho (189 * k) (9 * k)) ≤
      (9 / 20 : ℝ) ^ k * 2 := by
    rw [heq, div_eq_mul_one_div]
    exact mul_le_mul hpow hfactor.le
      (one_div_nonneg.mpr (by linarith)) (by positivity)
  have h := total_boxes_le_unpadded (L := 189 * k) (m := 9 * k) (t := k)
    (by omega) (by omega) hN
  calc ((tiles (189 * k) (9 * k) N).card : ℝ) *
        ((boxes (189 * k) (9 * k) k).card : ℝ)
      ≤ 16 * ((9 * k : ℕ) + 1 : ℝ) *
          (rho (189 * k) (9 * k) ^ k / (1 - rho (189 * k) (9 * k))) * (N : ℝ) ^ 2 := by
        simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] using h
    _ ≤ 16 * ((9 * k : ℕ) + 1 : ℝ) * ((9 / 20 : ℝ) ^ k * 2) * (N : ℝ) ^ 2 := by
      gcongr
    _ = _ := by ring

end Cslib.Algorithms.MatrixMultiplication.Schonhage.BoxTradeoff
