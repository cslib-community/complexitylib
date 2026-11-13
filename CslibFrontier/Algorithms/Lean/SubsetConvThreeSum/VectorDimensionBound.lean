/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.SubsetConvThreeSum.VectorDimension
import CslibFrontier.Foundations.Data.Nat.Log

/-!
# Upper bounds on the input-computed dimension and trials

The dimension `d = vDim r n L` of `CslibFrontier.Algorithms.Lean.SubsetConvThreeSum.VectorDimension`
is the least multiple `r j` of `r` meeting `480 (r!)^j n L ≤ (r^(r j) - 1) r^(r j)`. Minimality
(`vDimIndex_min`) bounds it from above, which is what the source's parameter analysis needs
([ChanItakuraMaYu2026], Theorem 3.4: `p₀² = r^(2d) ≈ 4 n̂² lg² N (r!)^{d/r}`):

* `pow_two_mul_vDim_le`: `r ^ (2 d) ≤ r ^ (2 r) (960 (r!)^(j - 1) n L + 1)`;
* `three_mul_vTrials_vDim_le`: the number of trials `μ = vTrials k e r d` satisfies
  `3 r ^ d (r!)^j μ ≤ 64 k (d + 1) ^ r r ^ (2 r) (960 (r!)^(j - 1) n L + 1) + 3 r ^ d (r!)^j`,
  an explicit bound in terms of `r`, `k`, `n`, `L` and `d` only.

These are finite inequalities. The source's closed forms `d = 2 log_ρ n̂ + O(log log N)` and
`μ = Õ(n̂² / r^d)` are not derived from them here.

## Main results

* `Cslib.Algorithms.Lean.SubsetConvThreeSum.pow_two_mul_vDim_le`,
  `three_mul_vTrials_vDim_le`.

## References

* [T. M. Chan, R. Itakura, Z. Ma, Y. Yu, *3SUM Made Simpler (Without Matrix Multiplication),
  k-SUM Hypothesis Refuted for Odd k, and Real 3SUM/APSP Derandomized*][ChanItakuraMaYu2026]
-/

public section

namespace Cslib.Algorithms.Lean.SubsetConvThreeSum

open Finset Nat

/-- **The dimension is not too large**: `r ^ (2 d) ≤ r ^ (2 r) (960 (r!)^(j - 1) n L + 1)` for
`d = vDim r n L = r j` and `r ≥ 2`. -/
theorem pow_two_mul_vDim_le {r : ℕ} (hr : 2 ≤ r) (n L : ℕ) :
    r ^ (2 * vDim r n L) ≤
      r ^ (2 * r) * (960 * (r !) ^ (vDimIndex r n L - 1) * (n * L) + 1) := by
  set j := vDimIndex r n L
  have hj1 := (vDimIndex_spec hr n L).1
  have hd : 2 * vDim r n L = 2 * r + 2 * (r * (j - 1)) := by
    change 2 * (r * j) = _
    obtain ⟨i, hi⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [hi]; simp; ring
  rw [hd, pow_add]
  refine Nat.mul_le_mul_left _ ?_
  rcases Nat.lt_or_ge j 2 with hj | hj
  · have : j - 1 = 0 := by omega
    rw [this]; simp
  · have hfail := vDimIndex_min hr n L (j := j - 1) (by omega)
    simp only [vDimCond, not_and, not_le] at hfail
    have hlt := hfail (by omega)
    set R := r ^ (r * (j - 1))
    have hR : 2 ≤ R := by
      calc 2 ≤ r := hr
        _ = r ^ 1 := (pow_one r).symm
        _ ≤ R := Nat.pow_le_pow_right (by omega) (Nat.mul_pos (by omega) (by omega))
    have h2 : R * R ≤ 2 * ((R - 1) * R) := by
      have : R ≤ 2 * (R - 1) := by omega
      calc R * R ≤ 2 * (R - 1) * R := Nat.mul_le_mul_right _ this
        _ = _ := by ring
    have : r ^ (2 * (r * (j - 1))) = R * R := by rw [← pow_add]; ring_nf
    rw [this]
    set X := (r !) ^ (j - 1) * (n * L)
    have hlt' : (R - 1) * R < 480 * X := by simpa only [X, mul_assoc] using hlt
    have : 960 * (r !) ^ (j - 1) * (n * L) = 2 * (480 * X) := by simp only [X]; ring
    rw [this]
    omega

/-- **Explicit number of trials**: for `d = vDim r n L = r j`, `e = ⌈log₂ r ^ d⌉` and
`μ = vTrials k e r d`,
`3 r ^ d (r!)^j μ ≤ 64 k (d + 1) ^ r r ^ (2 r) (960 (r!)^(j - 1) n L + 1) + 3 r ^ d (r!)^j`. -/
theorem three_mul_vTrials_vDim_le {r : ℕ} (hr : 2 ≤ r) (k n L : ℕ) :
    let d := vDim r n L
    let j := vDimIndex r n L
    let e := Nat.clog 2 (r ^ d)
    3 * r ^ d * (r !) ^ j * vTrials k e r d ≤
      64 * k * (d + 1) ^ r * (r ^ (2 * r) * (960 * (r !) ^ (j - 1) * (n * L) + 1)) +
        3 * r ^ d * (r !) ^ j := by
  intro d j e
  have hj1 := (vDimIndex_spec hr n L).1
  have hdr : d / r = j := Nat.mul_div_cancel_left j (by omega)
  have hrd2 : 2 ≤ r ^ d := by
    calc 2 ≤ r := hr
      _ = r ^ 1 := (pow_one r).symm
      _ ≤ r ^ d := Nat.pow_le_pow_right (by omega) (Nat.mul_pos (by omega) (by omega))
  have htr := three_mul_vTrials_le (k := k) (e := e) (r := r) (d := d) (by omega)
    (dvd_mul_right r j)
  rw [hdr] at htr
  have h4 : 4 ^ (e + 2) ≤ 64 * r ^ (2 * d) := by
    have h2 : 2 ^ e ≤ 2 * r ^ d := Nat.pow_clog_le_mul (by norm_num) (by omega)
    have hsq : 4 ^ e ≤ 4 * (r ^ d) ^ 2 := by
      calc 4 ^ e = 2 ^ e * 2 ^ e := by rw [← mul_pow]; norm_num
        _ ≤ (2 * r ^ d) * (2 * r ^ d) := Nat.mul_le_mul h2 h2
        _ = _ := by ring
    calc 4 ^ (e + 2) = 16 * 4 ^ e := by rw [pow_add]; ring
      _ ≤ 16 * (4 * (r ^ d) ^ 2) := Nat.mul_le_mul_left _ hsq
      _ = 64 * r ^ (2 * d) := by rw [← pow_mul]; ring_nf
  have hdim := pow_two_mul_vDim_le hr n L
  refine htr.trans (Nat.add_le_add_right ?_ _)
  calc k * 4 ^ (e + 2) * (d + 1) ^ r ≤ k * (64 * r ^ (2 * d)) * (d + 1) ^ r := by gcongr
    _ ≤ k * (64 * (r ^ (2 * r) * (960 * (r !) ^ (j - 1) * (n * L) + 1))) * (d + 1) ^ r := by
        gcongr
    _ = _ := by ring

end Cslib.Algorithms.Lean.SubsetConvThreeSum
