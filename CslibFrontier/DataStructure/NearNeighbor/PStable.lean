/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.NearNeighbor.MeasureLSH
public import CslibFrontier.Probability.LocalitySensitiveHash.PStable

/-!
# Approximate near neighbours in `\ell_2` and `\ell_1` via `p`-stable LSH

Instantiates `CslibFrontier.DataStructure.NearNeighbor.MeasureLSH` with the `p = 2` (Gaussian)
and `p = 1` (Cauchy) `p`-stable LSH families of [DatarImmorlicaIndykMirrokni2004]. Because both
`p2StableProb w d` and `p1StableProb w d` are strictly positive and strictly decreasing in `d ≥ 0`
for any bucket width `w > 0`, choosing `p₁ = p(d)` and `p₂ = p(c d)` with `0 < d` and `1 < c`
yields `0 < p₂ < p₁ ≤ 1`, sublinear exponent `ρ < 1`, and failure probability at most
`e⁻¹ + 1 / 3` using `numHashes`, `numTables`, and the `3 L` candidate stopping rule.

## Main results

* `Cslib.DataStructure.NearNeighbor.rho_p2Stable_lt_one`,
  `Cslib.DataStructure.NearNeighbor.measureReal_query_p2Stable_eq_none_le`: sublinear LSH
  exponent and `(c, d)`-approximate near-neighbour guarantee in Euclidean space (`p = 2`).
* `Cslib.DataStructure.NearNeighbor.rho_p1Stable_lt_one`,
  `Cslib.DataStructure.NearNeighbor.measureReal_query_p1Stable_eq_none_le`: sublinear LSH
  exponent and `(c, d)`-approximate near-neighbour guarantee in `\ell_1` (`p = 1`).

## References

* [M. Datar, N. Immorlica, P. Indyk, V. S. Mirrokni, *Locality-sensitive hashing scheme based on
  p-stable distributions*][DatarImmorlicaIndykMirrokni2004]
* [S. Har-Peled, P. Indyk, R. Motwani, *Approximate Nearest Neighbor: Towards Removing the Curse
  of Dimensionality*][HarPeledIndykMotwani2012], Section 3.
-/

public section

namespace Cslib.DataStructure.NearNeighbor

open Cslib.Probability MeasureTheory ProbabilityTheory Real

/-! ### `p = 2`: Euclidean `(c, d)`-near neighbours -/

/-- The LSH exponent for Gaussian `p = 2` hashing satisfies `ρ < 1` whenever `w > 0`, `d > 0`,
and `c > 1`. -/
theorem rho_p2Stable_lt_one {w d c : ℝ} (hw : 0 < w) (hd : 0 < d) (hc : 1 < c) :
    rho (p2StableProb w d) (p2StableProb w (c * d)) < 1 :=
  rho_lt_one (p2StableProb_pos hw (mul_nonneg (one_pos.trans hc).le hd.le))
    (p2StableProb_strictAnti hw hd.le (lt_mul_of_one_lt_left hd hc))
    (p2StableProb_le_one hw hd.le)

section Euclidean

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **The `(c, d)`-near-neighbour guarantee in Euclidean space.** Using `p2StableHash w` on `E`
with `0 < w`, `0 < d`, `1 < c`, `p₁ = p2StableProb w d`, `p₂ = p2StableProb w (c d)`,
`k = numHashes n p₂`, `L = numTables n p₁ p₂`, and `T = 3 L`, if some point of `P` is within
distance `d` of `q`, the query fails with probability at most `e⁻¹ + 1 / 3`; any returned point is
within distance `c d` (`query_eq_some`). -/
theorem measureReal_query_p2Stable_eq_none_le {w d c : ℝ} (hw : 0 < w) (hd : 0 < d) (hc : 1 < c)
    {P : List E} {q x₀ : E} (hx₀ : x₀ ∈ P) (hnear : ‖x₀ - q‖ ≤ d) :
    (Measure.pi fun _ : Fin (numTables P.length (p2StableProb w d) (p2StableProb w (c * d))) =>
        Measure.pi fun _ : Fin (numHashes P.length (p2StableProb w (c * d))) =>
          (stdGaussian E).prod (uniformInterval w)).real
        {s | query (andHash (p2StableHash w) (numHashes P.length (p2StableProb w (c * d))))
          (fun x y => c * d ≤ ‖x - y‖) s
          (3 * numTables P.length (p2StableProb w d) (p2StableProb w (c * d))) P q = none} ≤
      Real.exp (-1) + 1 / 3 := by
  have := isProbabilityMeasure_uniformInterval hw
  exact measureReal_query_numTables_eq_none_le
    (isLocalitySensitive_p2StableHash (E := E) hw d (mul_nonneg (one_pos.trans hc).le hd.le))
    (p2StableProb_pos hw (mul_nonneg (one_pos.trans hc).le hd.le))
    (p2StableProb_strictAnti hw hd.le (lt_mul_of_one_lt_left hd hc))
    (p2StableProb_le_one hw hd.le) hx₀
    (fun x _ => measurableSet_p2StableHash_eq w x q) hnear

end Euclidean

/-! ### `p = 1`: `\ell_1` `(c, d)`-near neighbours -/

/-- The LSH exponent for Cauchy `p = 1` hashing satisfies `ρ < 1` whenever `w > 0`, `d > 0`,
and `c > 1`. -/
theorem rho_p1Stable_lt_one {w d c : ℝ} (hw : 0 < w) (hd : 0 < d) (hc : 1 < c) :
    rho (p1StableProb w d) (p1StableProb w (c * d)) < 1 :=
  rho_lt_one (p1StableProb_pos hw (mul_nonneg (one_pos.trans hc).le hd.le))
    (p1StableProb_strictAnti hw hd.le (lt_mul_of_one_lt_left hd hc))
    (p1StableProb_le_one hw hd.le)

/-- **The `(c, d)`-near-neighbour guarantee in `\ell_1`.** Using `p1StableHash w` on `ι → ℝ`
with `0 < w`, `0 < d`, `1 < c`, `p₁ = p1StableProb w d`, `p₂ = p1StableProb w (c d)`,
`k = numHashes n p₂`, `L = numTables n p₁ p₂`, and `T = 3 L`, if some point of `P` has `\ell_1`
distance at most `d` to `q`, the query fails with probability at most `e⁻¹ + 1 / 3`; any returned
point has `\ell_1` distance below `c d` (`query_eq_some`). -/
theorem measureReal_query_p1Stable_eq_none_le {ι : Type*} [Fintype ι] {w d c : ℝ} (hw : 0 < w)
    (hd : 0 < d) (hc : 1 < c) {P : List (ι → ℝ)} {q x₀ : ι → ℝ} (hx₀ : x₀ ∈ P)
    (hnear : ∑ i, |x₀ i - q i| ≤ d) :
    (Measure.pi fun _ : Fin (numTables P.length (p1StableProb w d) (p1StableProb w (c * d))) =>
        Measure.pi fun _ : Fin (numHashes P.length (p1StableProb w (c * d))) =>
          (Measure.pi fun _ : ι => cauchyMeasure 0 1).prod (uniformInterval w)).real
        {s | query (andHash (p1StableHash w) (numHashes P.length (p1StableProb w (c * d))))
          (fun x y => c * d ≤ ∑ i, |x i - y i|) s
          (3 * numTables P.length (p1StableProb w d) (p1StableProb w (c * d))) P q = none} ≤
      Real.exp (-1) + 1 / 3 := by
  have := isProbabilityMeasure_uniformInterval hw
  exact measureReal_query_numTables_eq_none_le
    (isLocalitySensitive_p1StableHash (ι := ι) hw d (mul_nonneg (one_pos.trans hc).le hd.le))
    (p1StableProb_pos hw (mul_nonneg (one_pos.trans hc).le hd.le))
    (p1StableProb_strictAnti hw hd.le (lt_mul_of_one_lt_left hd hc))
    (p1StableProb_le_one hw hd.le) hx₀
    (fun x _ => measurableSet_p1StableHash_eq w x q) hnear

end Cslib.DataStructure.NearNeighbor
