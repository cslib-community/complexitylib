/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.DataStructure.NearNeighbor.LSH
public import Complexity.Probability.LocalitySensitiveHash.BitSampling
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Approximate near neighbours in Hamming space

Bit sampling is `(r, c r, 1 - r / d, 1 - c r / d)`-sensitive for the Hamming distance on words of
length `d` (`Cslib.Probability.isLocalitySensitive_bitSampling`). Its exponent satisfies
`ρ ≤ 1 / c` ([IndykMotwani1998]; [HarPeledIndykMotwani2012], Section 3.2.1). The function
`t ↦ log (1 - t)` is concave and vanishes at `0`, so `log (1 - r / d) ≥ log (1 - c r / d) / c`
(`Cslib.DataStructure.NearNeighbor.rho_one_sub_le`). With the parameters of
`Cslib.DataStructure.NearNeighbor.toOuterMeasure_query_numTables_eq_none_le`, the
`(c, r)`-near neighbour query on `n` words fails with probability at most `e⁻¹ + 1 / 3`
(`toOuterMeasure_query_bitSampling_eq_none_le`). It uses `L < n ^ (1 / c) / p₁ + 1` tables
(`numTables_bitSampling_lt`), the table count behind the `n ^ (1 / c)` query bound of Indyk and
Motwani for the Hamming cube. The query time itself is not formalized (see the module
`Complexity.DataStructure.NearNeighbor.LSH`).

## Main results

* `Cslib.DataStructure.NearNeighbor.rho_one_sub_le`: `ρ(1 - a, 1 - c a) ≤ 1 / c`.
* `Cslib.DataStructure.NearNeighbor.toOuterMeasure_query_bitSampling_eq_none_le`: the
  `(c, r)`-near-neighbour guarantee for bit sampling.
* `Cslib.DataStructure.NearNeighbor.numTables_bitSampling_lt`: `L < n ^ (1 / c) / p₁ + 1`.

## References

* [P. Indyk, R. Motwani, *Approximate Nearest Neighbors: Towards Removing the Curse of
  Dimensionality*][IndykMotwani1998]
* [S. Har-Peled, P. Indyk, R. Motwani, *Approximate Nearest Neighbor: Towards Removing the Curse
  of Dimensionality*][HarPeledIndykMotwani2012], Section 3.2.1.
-/

public section

namespace Cslib.DataStructure.NearNeighbor

open Cslib.Probability

/-- **`ρ ≤ 1 / c` for bit sampling**: for `0 < a` and `1 < c` with `c a < 1`,
`log (1 / (1 - a)) / log (1 / (1 - c a)) ≤ 1 / c`. -/
theorem rho_one_sub_le {a c : ℝ} (ha : 0 < a) (hc : 1 < c) (hca : c * a < 1) :
    rho (1 - a) (1 - c * a) ≤ 1 / c := by
  have hc0 : 0 < c := one_pos.trans hc
  have hb : 0 < 1 - c * a := by linarith
  have hw : 0 ≤ 1 - 1 / c := by
    rw [sub_nonneg, div_le_one hc0]
    exact hc.le
  -- concavity of `log` between `1 - c a` and `1`
  have hconc := strictConcaveOn_log_Ioi.concaveOn.2 (Set.mem_Ioi.2 hb) (Set.mem_Ioi.2 one_pos)
    (one_div_pos.2 hc0).le hw (by ring)
  have hpt : (1 / c) • (1 - c * a) + (1 - 1 / c) • (1 : ℝ) = 1 - a := by
    simp only [smul_eq_mul]
    field_simp
    ring
  rw [hpt, smul_eq_mul, smul_eq_mul, Real.log_one, mul_zero, add_zero] at hconc
  have hlog : Real.log (1 - c * a) < 0 := Real.log_neg hb (by linarith [mul_pos hc0 ha])
  rw [rho, one_div (1 - a), one_div (1 - c * a), Real.log_inv, Real.log_inv, neg_div_neg_eq,
    div_le_iff_of_neg hlog]
  linarith

variable {κ : Type*} [Fintype κ] [Nonempty κ] {β : Type*} [DecidableEq β]

/-- **The `(c, r)`-near-neighbour guarantee in Hamming space.** Bit sampling on words of length
`d = |κ|`, with `0 < r`, `1 < c` and `c r < d`, and the parameters `k = numHashes n p₂`,
`L = numTables n p₁ p₂`, `T = 3 L` for `p₁ = 1 - r / d` and `p₂ = 1 - c r / d`. If some word of `P`
is within distance `r` of `q`, the query fails with probability at most `e⁻¹ + 1 / 3`. Its answers
are within distance `c r` of `q` (`query_eq_some`). -/
theorem toOuterMeasure_query_bitSampling_eq_none_le {r c : ℝ} (hr : 0 < r) (hc : 1 < c)
    (hcr : c * r < Fintype.card κ) {P : List (κ → β)} {q x₀ : κ → β} (hx₀ : x₀ ∈ P)
    (hnear : (hammingDist x₀ q : ℝ) ≤ r) :
    ((PMF.iid (PMF.iid (PMF.uniformOfFintype κ)
        (numHashes P.length (1 - c * r / Fintype.card κ)))
        (numTables P.length (1 - r / Fintype.card κ) (1 - c * r / Fintype.card κ))).toOuterMeasure
        {s | query (andHash (fun i (z : κ → β) => z i)
          (numHashes P.length (1 - c * r / Fintype.card κ)))
          (fun x y => c * r ≤ (hammingDist x y : ℝ)) s
          (3 * numTables P.length (1 - r / Fintype.card κ) (1 - c * r / Fintype.card κ)) P q =
            none}).toReal ≤ Real.exp (-1) + 1 / 3 := by
  have hd : (0 : ℝ) < Fintype.card κ := by exact_mod_cast Fintype.card_pos
  have hc0 : 0 < c := one_pos.trans hc
  refine toOuterMeasure_query_numTables_eq_none_le (isLocalitySensitive_bitSampling r (c * r))
    ?_ ?_ ?_ hx₀ hnear
  · rw [sub_pos, div_lt_one hd]
    exact hcr
  · have : r < c * r := by nlinarith
    linarith [div_lt_div_of_pos_right this hd]
  · linarith [div_pos hr hd]

/-- With bit sampling, the number of tables is `L < n ^ (1 / c) / p₁ + 1`. -/
theorem numTables_bitSampling_lt {r c d : ℝ} (hr : 0 < r) (hc : 1 < c) (hcr : c * r < d)
    {n : ℕ} (hn : 0 < n) :
    (numTables n (1 - r / d) (1 - c * r / d) : ℝ) < (n : ℝ) ^ (1 / c) / (1 - r / d) + 1 := by
  have hc0 : 0 < c := one_pos.trans hc
  have hd : 0 < d := by nlinarith
  have hrd : r / d < 1 := by
    rw [div_lt_one hd]
    nlinarith
  have hp₁ : 0 < 1 - r / d := by linarith
  have hρ : rho (1 - r / d) (1 - c * r / d) ≤ 1 / c := by
    have h := rho_one_sub_le (div_pos hr hd) hc (by rw [← mul_div_assoc, div_lt_one hd]; exact hcr)
    rwa [← mul_div_assoc] at h
  have hpow : (n : ℝ) ^ rho (1 - r / d) (1 - c * r / d) ≤ (n : ℝ) ^ (1 / c) :=
    Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.2 hn) hρ
  have := div_le_div_of_nonneg_right hpow hp₁.le
  linarith [numTables_lt n (p₂ := 1 - c * r / d) hp₁]

end Cslib.DataStructure.NearNeighbor
