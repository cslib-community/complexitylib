/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.NearNeighbor.MeasureLSH
public import CslibFrontier.Probability.LocalitySensitiveHash.SimHash
import CslibFrontier.DataStructure.NearNeighbor.Hamming

/-!
# Approximate near neighbours in angular distance via SimHash

SimHash is `(θ, c θ, 1 - θ / π, 1 - c θ / π)`-sensitive for the angular distance on nonzero
vectors (`Cslib.Probability.isLocalitySensitive_simHash_subtype`). By concavity of `log`, its LSH
exponent satisfies `ρ ≤ 1 / c` (`Cslib.DataStructure.NearNeighbor.rho_simHash_le`), and plugging
it into `measureReal_query_numTables_eq_none_le` yields a `(c, θ)`-approximate angular
near-neighbour guarantee with failure probability at most `e⁻¹ + 1 / 3`
(`measureReal_query_simHash_eq_none_le`).

## Main results

* `Cslib.DataStructure.NearNeighbor.rho_simHash_le`: `ρ(1 - θ / π, 1 - c θ / π) ≤ 1 / c`.
* `Cslib.DataStructure.NearNeighbor.measureReal_query_simHash_eq_none_le`: the `(c, θ)`-angular
  near-neighbour guarantee for SimHash.
* `Cslib.DataStructure.NearNeighbor.numTables_simHash_lt`: `L < n ^ (1 / c) / (1 - θ / π) + 1`.

## References

* [M. S. Charikar, *Similarity estimation techniques from rounding algorithms*][Charikar2002]
* [P. Indyk, R. Motwani, *Approximate Nearest Neighbors: Towards Removing the Curse of
  Dimensionality*][IndykMotwani1998]
-/

public section

namespace Cslib.DataStructure.NearNeighbor

open Cslib.Probability MeasureTheory ProbabilityTheory Real

/-- **`ρ ≤ 1 / c` for SimHash**: for `0 < θ`, `1 < c`, and `c θ < π`,
`log (1 / (1 - θ / π)) / log (1 / (1 - c θ / π)) ≤ 1 / c`. -/
theorem rho_simHash_le {θ c : ℝ} (hθ : 0 < θ) (hc : 1 < c) (hcθ : c * θ < π) :
    rho (1 - θ / π) (1 - c * θ / π) ≤ 1 / c := by
  have hcθ' : c * (θ / π) < 1 := by
    rw [← mul_div_assoc, div_lt_one pi_pos]
    exact hcθ
  rw [mul_div_assoc]
  exact rho_one_sub_le (div_pos hθ pi_pos) hc hcθ'

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **The `(c, θ)`-near-neighbour guarantee in angular distance.** SimHash on nonzero vectors of
`E`, with `0 < θ`, `1 < c`, `c θ < π`, `p₁ = 1 - θ / π`, `p₂ = 1 - c θ / π`,
`k = numHashes n p₂`, `L = numTables n p₁ p₂`, and `T = 3 L`. If some point of `P` makes angle at
most `θ` with `q`, the query fails with probability at most `e⁻¹ + 1 / 3`; any answer has angle
below `c θ` with `q` (`query_eq_some`). -/
theorem measureReal_query_simHash_eq_none_le {θ c : ℝ} (hθ : 0 < θ) (hc : 1 < c)
    (hcθ : c * θ < π) {P : List {x : E // x ≠ 0}} {q x₀ : {x : E // x ≠ 0}} (hx₀ : x₀ ∈ P)
    (hnear : InnerProductGeometry.angle x₀.1 q.1 ≤ θ) :
    (Measure.pi fun _ : Fin (numTables P.length (1 - θ / π) (1 - c * θ / π)) =>
        Measure.pi fun _ : Fin (numHashes P.length (1 - c * θ / π)) => stdGaussian E).real
        {s | query (andHash (fun r (u : {x : E // x ≠ 0}) => simHash r u.1)
            (numHashes P.length (1 - c * θ / π)))
          (fun x y => c * θ ≤ InnerProductGeometry.angle x.1 y.1) s
          (3 * numTables P.length (1 - θ / π) (1 - c * θ / π)) P q = none} ≤
      Real.exp (-1) + 1 / 3 := by
  have hc0 : 0 < c := one_pos.trans hc
  refine measureReal_query_numTables_eq_none_le
    (isLocalitySensitive_simHash_subtype (E := E) θ (c * θ)) ?_ ?_ ?_ hx₀
    (fun x _ => measurableSet_simHash_eq x.1 q.1) hnear
  · rw [sub_pos, div_lt_one pi_pos]
    exact hcθ
  · have : θ < c * θ := by nlinarith
    linarith [div_lt_div_of_pos_right this pi_pos]
  · linarith [div_pos hθ pi_pos]

/-- With SimHash, the number of tables satisfies `L < n ^ (1 / c) / (1 - θ / π) + 1`. -/
theorem numTables_simHash_lt {n : ℕ} (hn : 0 < n) {θ c : ℝ} (hθ : 0 < θ) (hc : 1 < c)
    (hcθ : c * θ < π) :
    (numTables n (1 - θ / π) (1 - c * θ / π) : ℝ) < (n : ℝ) ^ (1 / c) / (1 - θ / π) + 1 := by
  have hp₁ : 0 < 1 - θ / π := by
    have : θ < π := by nlinarith
    linarith [div_lt_one pi_pos |>.mpr this]
  refine (numTables_lt n hp₁).trans_le ?_
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  gcongr
  exact rho_simHash_le hθ hc hcθ

end Cslib.DataStructure.NearNeighbor
