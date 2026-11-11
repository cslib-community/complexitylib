/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.DataStructure.NearNeighbor.Angular
import CslibFrontier.DataStructure.NearNeighbor.PStable
import CslibFrontier.Foundations.Geometry.Euclidean.Angle.Unoriented.Basic
import CslibFrontier.Probability.LocalitySensitiveHash.BitSampling
import CslibFrontier.Probability.LocalitySensitiveHash.Measure

/-!
# Tests for Continuous-Seed LSH, SimHash, and `p`-Stable LSH

Concrete, non-vacuous checks exercising:
1. Measure-theoretic LSH primitives (`measureCollisionProb_toMeasure`,
   `measureCollisionProb_triangle`, `IsLocalitySensitive.measureBanded`,
   `measureOrCollisionProb_andHash`).
2. `uniformInterval` quantization (`measureReal_uniformInterval_floor_eq`) on overlapping and
   disjoint intervals.
3. Charikar's SimHash (`simHash`, `measureCollisionProb_simHash`,
   `measureCollisionProb_simHash_of_norm_eq_one`, `measureCollisionProb_simHash_pi`,
   `isLocalitySensitive_simHash_inner`, a counterexample showing non-vacuity of sensitivity,
   `rho_simHash_le`, `numTables_simHash_lt`, and `measureReal_query_simHash_eq_none_le`).
4. Cauchy `1`-stability (`cauchyMeasure_map_const_mul`, `pi_cauchyMeasure_map_dotProduct`) and
   `p = 1` / `p = 2` `p`-stable LSH (`p2StableProb`, `p1StableProb`, exact values, strict
   monotonicity, collision laws, `rho_p2Stable_lt_one`, `rho_p1Stable_lt_one`, and both
   `(c, r)`-ANN bounds).
-/

namespace CslibFrontierTests.LSHContinuous

open Cslib.Probability Cslib.DataStructure.NearNeighbor MeasureTheory ProbabilityTheory Real
open scoped RealInnerProductSpace

section BasisHelpers

private noncomputable def e0 : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![1, 0]
private noncomputable def e1 : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![0, 1]
private noncomputable def u45 : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![√2 / 2, √2 / 2]

private theorem e0_norm : ‖e0‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp only [e0, Fin.sum_univ_two]
  norm_num

private theorem e1_norm : ‖e1‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp only [e1, Fin.sum_univ_two]
  norm_num

private theorem u45_norm : ‖u45‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp only [u45, Fin.sum_univ_two, WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_one,
    Real.norm_eq_abs, sq_abs]
  rw [div_pow, Real.sq_sqrt zero_le_two]
  norm_num

private theorem e0_ne_zero : e0 ≠ 0 := by
  rw [← norm_ne_zero_iff, e0_norm]
  exact one_ne_zero

private theorem e1_ne_zero : e1 ≠ 0 := by
  rw [← norm_ne_zero_iff, e1_norm]
  exact one_ne_zero

private theorem u45_ne_zero : u45 ≠ 0 := by
  rw [← norm_ne_zero_iff, u45_norm]
  exact one_ne_zero

private theorem e0_e1_inner : ⟪e0, e1⟫ = (0 : ℝ) := by
  rw [PiLp.inner_apply]
  simp only [e0, e1, Fin.sum_univ_two, WithLp.ofLp_toLp, Matrix.cons_val_zero,
    Matrix.cons_val_one, inner_zero_right, inner_zero_left, add_zero]

private theorem e0_u45_inner : ⟪e0, u45⟫ = √2 / 2 := by
  rw [PiLp.inner_apply]
  simp only [e0, u45, Fin.sum_univ_two, WithLp.ofLp_toLp, Matrix.cons_val_zero,
    Matrix.cons_val_one, RCLike.inner_apply, conj_trivial, mul_zero, add_zero, mul_one]

private theorem angle_e0_e1 : InnerProductGeometry.angle e0 e1 = π / 2 := by
  rw [InnerProductGeometry.angle_eq_arccos_inner_of_norm_eq_one e0_norm e1_norm, e0_e1_inner,
    Real.arccos_zero]

private theorem angle_e0_u45 : InnerProductGeometry.angle e0 u45 = π / 4 := by
  rw [InnerProductGeometry.angle_eq_arccos_inner_of_norm_eq_one e0_norm u45_norm, e0_u45_inner,
    ← Real.cos_pi_div_four, Real.arccos_cos (by positivity) (by linarith [pi_pos])]

end BasisHelpers

/-! ### Measure-theoretic LSH primitives -/

/-- Bridging a discrete uniform `PMF` on `Fin 4` to `PMF.toMeasure` reproduces `1 / 2`. -/
example :
    measureCollisionProb (PMF.uniformOfFintype (Fin 4)).toMeasure
      (fun i (z : Fin 4 → Bool) => z i)
      (fun i => decide (i.val < 2)) (fun _ => false) = 1 / 2 := by
  rw [measureCollisionProb_toMeasure _ _ (MeasurableSet.of_discrete), collisionProb_bitSampling]
  have hd : hammingDist (fun i : Fin 4 => decide (i.val < 2)) (fun _ => false) = 2 := by decide
  rw [hd]
  norm_num

/-- Charikar's triangle inequality for SimHash on `(e0, u45, e1)`. -/
example :
    1 - measureCollisionProb (stdGaussian (EuclideanSpace ℝ (Fin 2))) simHash e0 e1 ≤
      (1 - measureCollisionProb (stdGaussian (EuclideanSpace ℝ (Fin 2))) simHash e0 u45) +
        (1 - measureCollisionProb (stdGaussian (EuclideanSpace ℝ (Fin 2))) simHash u45 e1) :=
  measureCollisionProb_triangle (stdGaussian (EuclideanSpace ℝ (Fin 2))) simHash
    (measurableSet_simHash_eq e0 u45)
    (measurableSet_simHash_eq u45 e1)
    (measurableSet_simHash_eq e0 e1)

/-- Measure-theoretic banding (`k = 2, L = 4`) applied to SimHash at angles `(π / 4, π / 2)`. -/
example :
    IsLocalitySensitive
      (measureOrCollisionProb (Measure.pi fun _ : Fin 2 => stdGaussian (EuclideanSpace ℝ (Fin 2)))
        (andHash simHash 2) 4)
      (fun u v => u ≠ 0 ∧ v ≠ 0 ∧ InnerProductGeometry.angle u v ≤ π / 4)
      (fun u v => u ≠ 0 ∧ v ≠ 0 ∧ π / 2 ≤ InnerProductGeometry.angle u v)
      (sCurve 2 4 (3 / 4)) (sCurve 2 4 (1 / 2)) := by
  have h := isLocalitySensitive_simHash (E := EuclideanSpace ℝ (Fin 2)) (π / 4) (π / 2)
  have hpi : π ≠ 0 := pi_ne_zero
  have h1 : (1 : ℝ) - π / 4 / π = 3 / 4 := by
    field_simp
    ring
  have h2 : (1 : ℝ) - π / 2 / π = 1 / 2 := by
    field_simp
    ring
  rw [h1, h2] at h
  exact h.measureBanded measurableSet_simHash_eq (by norm_num) (by norm_num) 2 4

/-! ### SimHash and angular `(c, θ)`-ANN -/

/-- Orthogonal vectors collide under SimHash with probability `1 / 2`. -/
theorem simHash_orthogonal_prob :
    measureCollisionProb (stdGaussian (EuclideanSpace ℝ (Fin 2))) simHash e0 e1 = 1 / 2 := by
  rw [measureCollisionProb_simHash e0_ne_zero e1_ne_zero, angle_e0_e1]
  have hpi : π ≠ 0 := pi_ne_zero
  field_simp
  ring

/-- Vectors at angle `π / 4` collide under SimHash with probability `3 / 4`. -/
theorem simHash_pi_div_four_prob :
    measureCollisionProb (stdGaussian (EuclideanSpace ℝ (Fin 2))) simHash e0 u45 = 3 / 4 := by
  rw [measureCollisionProb_simHash_of_norm_eq_one e0_norm u45_norm, e0_u45_inner,
    ← Real.cos_pi_div_four, Real.arccos_cos (by positivity) (by linarith [pi_pos])]
  have hpi : π ≠ 0 := pi_ne_zero
  field_simp
  ring

/-- Coordinate i.i.d. standard Gaussian SimHash matches `3 / 4` at `angle = π / 4`. -/
example :
    measureCollisionProb (Measure.pi fun _ : Fin 2 => gaussianReal 0 1)
      (fun a x => simHash (WithLp.toLp 2 a) x) e0 u45 = 3 / 4 := by
  rw [measureCollisionProb_simHash_pi e0_ne_zero u45_ne_zero, angle_e0_u45]
  have hpi : π ≠ 0 := pi_ne_zero
  field_simp
  ring

/-- SimHash on unit vectors is `(3 / 4, 1 / 2)`-sensitive for cosine similarity
`(√2 / 2 ≤ ⟪u, v⟫)` versus `(⟪u, v⟫ ≤ 0)` via `isLocalitySensitive_simHash_inner`. -/
example :
    IsLocalitySensitive
      (measureCollisionProb (stdGaussian (EuclideanSpace ℝ (Fin 2)))
        (fun r (u : {x : EuclideanSpace ℝ (Fin 2) // ‖x‖ = 1}) => simHash r u.1))
      (fun u v => √2 / 2 ≤ ⟪u.1, v.1⟫) (fun u v => ⟪u.1, v.1⟫ ≤ 0) (3 / 4) (1 / 2) := by
  have h := isLocalitySensitive_simHash_inner (E := EuclideanSpace ℝ (Fin 2)) (√2 / 2) 0
  have hpi : π ≠ 0 := pi_ne_zero
  have h1 : (1 : ℝ) - Real.arccos (√2 / 2) / π = 3 / 4 := by
    rw [← Real.cos_pi_div_four, Real.arccos_cos (by positivity) (by linarith [pi_pos])]
    field_simp
    ring
  have h2 : (1 : ℝ) - Real.arccos 0 / π = 1 / 2 := by
    rw [Real.arccos_zero]
    field_simp
    ring
  rw [h1, h2] at h
  exact h

/-- Non-vacuity: SimHash is NOT `(π / 3, π / 2, 2 / 3, 1 / 3)`-sensitive on nonzero vectors,
because orthogonal `e0, e1` have angle `π / 2` and collide with probability `1 / 2 > 1 / 3`. -/
example :
    ¬ IsLocalitySensitive (measureCollisionProb (stdGaussian (EuclideanSpace ℝ (Fin 2))) simHash)
      (fun u v => u ≠ 0 ∧ v ≠ 0 ∧ InnerProductGeometry.angle u v ≤ π / 3)
      (fun u v => u ≠ 0 ∧ v ≠ 0 ∧ π / 2 ≤ InnerProductGeometry.angle u v) (2 / 3) (1 / 3) := by
  intro h
  have hfar := h.le_of_far e0 e1 ⟨e0_ne_zero, e1_ne_zero, le_of_eq angle_e0_e1.symm⟩
  rw [simHash_orthogonal_prob] at hfar
  norm_num at hfar

/-- SimHash exponent bound and table bound for `θ = π / 4, c = 2` (`n = 16`). -/
example :
    rho (1 - (π / 4) / π) (1 - 2 * (π / 4) / π) ≤ 1 / 2 ∧
      (numTables 16 (1 - (π / 4) / π) (1 - 2 * (π / 4) / π) : ℝ) <
        (16 : ℝ) ^ (1 / (2 : ℝ)) / (1 - (π / 4) / π) + 1 := by
  refine ⟨rho_simHash_le (by positivity) one_lt_two (by linarith [pi_pos]),
    numTables_simHash_lt (by norm_num) (by positivity) one_lt_two (by linarith [pi_pos])⟩

/-- Concrete `(2, π / 4)`-angular near-neighbour query bound via SimHash. -/
example :
    let P : List {x : EuclideanSpace ℝ (Fin 2) // x ≠ 0} := [⟨e0, e0_ne_zero⟩, ⟨e1, e1_ne_zero⟩]
    (Measure.pi fun _ : Fin (numTables P.length (1 - (π / 4) / π) (1 - 2 * (π / 4) / π)) =>
        Measure.pi fun _ : Fin (numHashes P.length (1 - 2 * (π / 4) / π)) =>
          stdGaussian (EuclideanSpace ℝ (Fin 2))).real
        {s | query
            (andHash (fun r (u : {x : EuclideanSpace ℝ (Fin 2) // x ≠ 0}) => simHash r u.1)
              (numHashes P.length (1 - 2 * (π / 4) / π)))
            (fun x y => 2 * (π / 4) ≤ InnerProductGeometry.angle x.1 y.1) s
            (3 * numTables P.length (1 - (π / 4) / π) (1 - 2 * (π / 4) / π))
            P ⟨u45, u45_ne_zero⟩ = none} ≤
      Real.exp (-1) + 1 / 3 := by
  intro P
  exact measureReal_query_simHash_eq_none_le (θ := π / 4) (c := 2)
    (by positivity) one_lt_two (by linarith [pi_pos]) (P := P) (q := ⟨u45, u45_ne_zero⟩)
    (x₀ := ⟨e0, e0_ne_zero⟩) List.mem_cons_self angle_e0_u45.le

/-! ### `uniformInterval`, Cauchy `1`-stability, and `p`-stable LSH -/

/-- Exact `uniformInterval 2` floor-collision probabilities for overlapping (`1 / 2`) and
disjoint (`0`) scalars. -/
example :
    (uniformInterval 2).real {b : ℝ | ⌊(0.5 + b) / 2⌋ = ⌊(1.5 + b) / 2⌋} = 1 / 2 ∧
      (uniformInterval 2).real {b : ℝ | ⌊(0 + b) / 2⌋ = ⌊(3 + b) / 2⌋} = 0 := by
  refine ⟨?_, ?_⟩
  · rw [measureReal_uniformInterval_floor_eq (by norm_num)]
    norm_num
  · rw [measureReal_uniformInterval_floor_eq (by norm_num)]
    norm_num

/-- Concrete `2`-coordinate `1`-stability of i.i.d. standard Cauchy variables:
`3 X₀ - 4 X₁ ~ Cauchy(0, 7)`. -/
example :
    (Measure.pi fun _ : Fin 2 => cauchyMeasure 0 1).map (fun a => (3 : ℝ) * a 0 - 4 * a 1) =
      cauchyMeasure 0 7 := by
  have hfun : (fun a : Fin 2 → ℝ => (3 : ℝ) * a 0 - 4 * a 1) =
      fun a => (![(3 : ℝ), -4] ⬝ᵥ a) := by
    funext a
    simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  rw [hfun, pi_cauchyMeasure_map_dotProduct]
  congr 1
  apply NNReal.coe_injective
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

/-- Closed-form check for `p = 1`: `p1StableProb 1 1 = 1 / 2 - log 2 / π`, strictly positive and
strictly larger than `p1StableProb 1 2`. -/
example :
    p1StableProb 1 1 = 1 / 2 - Real.log 2 / π ∧
      0 < p1StableProb 1 2 ∧ p1StableProb 1 2 < p1StableProb 1 1 := by
  refine ⟨?_, p1StableProb_pos one_pos (by norm_num),
    p1StableProb_strictAnti one_pos one_pos.le one_lt_two⟩
  rw [p1StableProb_eq one_pos one_pos, div_one, Real.arctan_one, one_pow, mul_one,
    one_add_one_eq_two]
  have hpi : π ≠ 0 := pi_ne_zero
  field_simp
  ring

/-- Strict ordering and positivity of `p2StableProb`, plus concrete Euclidean collision law at
distance `5` (`‖![3, 0] - ![0, 4]‖ = 5`). -/
example :
    0 < p2StableProb 2 4 ∧ p2StableProb 2 4 < p2StableProb 2 2 ∧
      measureCollisionProb ((stdGaussian (EuclideanSpace ℝ (Fin 2))).prod (uniformInterval 2))
        (p2StableHash 2) (WithLp.toLp 2 ![3, 0]) (WithLp.toLp 2 ![0, 4]) =
          p2StableProb 2 5 := by
  refine ⟨p2StableProb_pos (by norm_num) (by norm_num),
    p2StableProb_strictAnti (by norm_num) (by norm_num) (by norm_num), ?_⟩
  have hnorm : ‖WithLp.toLp 2 (![3, 0] : Fin 2 → ℝ) - WithLp.toLp 2 (![0, 4] : Fin 2 → ℝ)‖ = 5 := by
    rw [EuclideanSpace.norm_eq]
    simp only [Fin.sum_univ_two]
    norm_num
    rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [measureCollisionProb_p2StableHash (by norm_num), hnorm]

/-- Concrete `\ell_1` Cauchy collision probability at distance `7` (`|1 - 4| + |2 - (-2)| = 7`). -/
example :
    measureCollisionProb
        ((Measure.pi fun _ : Fin 2 => cauchyMeasure 0 1).prod (uniformInterval 2))
        (p1StableHash 2) ![1, 2] ![4, -2] =
      p1StableProb 2 7 := by
  have hl1 : ∑ i : Fin 2, |(![1, 2] : Fin 2 → ℝ) i - ![4, -2] i| = 7 := by
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  rw [measureCollisionProb_p1StableHash (by norm_num), hl1]

/-- Sublinear `ρ < 1` and concrete `(2, 1)`-ANN query bounds for both `p = 2` (Euclidean) and
`p = 1` (`\ell_1`). -/
example :
    rho (p2StableProb 2 1) (p2StableProb 2 (2 * 1)) < 1 ∧
      rho (p1StableProb 2 1) (p1StableProb 2 (2 * 1)) < 1 :=
  ⟨rho_p2Stable_lt_one (by norm_num) one_pos one_lt_two,
    rho_p1Stable_lt_one (by norm_num) one_pos one_lt_two⟩

/-- Concrete Euclidean `(2, 1)`-near-neighbour query failure bound using `p2StableHash 2`. -/
example :
    let P : List (EuclideanSpace ℝ (Fin 2)) := [e0, 5 • e0]
    (Measure.pi fun _ : Fin (numTables P.length (p2StableProb 2 1) (p2StableProb 2 (2 * 1))) =>
        Measure.pi fun _ : Fin (numHashes P.length (p2StableProb 2 (2 * 1))) =>
          (stdGaussian (EuclideanSpace ℝ (Fin 2))).prod (uniformInterval 2)).real
        {s | query (andHash (p2StableHash 2) (numHashes P.length (p2StableProb 2 (2 * 1))))
          (fun x y => 2 * 1 ≤ ‖x - y‖) s
          (3 * numTables P.length (p2StableProb 2 1) (p2StableProb 2 (2 * 1)))
          P e0 = none} ≤
      Real.exp (-1) + 1 / 3 := by
  intro P
  exact measureReal_query_p2Stable_eq_none_le (w := 2) (d := 1) (c := 2)
    (by norm_num) one_pos one_lt_two (P := P) (q := e0) (x₀ := e0) List.mem_cons_self
    (by simp only [sub_self, norm_zero, zero_le_one])

/-- Concrete `\ell_1` `(2, 1)`-near-neighbour query failure bound using `p1StableHash 2`. -/
example :
    let P : List (Fin 2 → ℝ) := [![0, 0], ![5, 0]]
    (Measure.pi fun _ : Fin (numTables P.length (p1StableProb 2 1) (p1StableProb 2 (2 * 1))) =>
        Measure.pi fun _ : Fin (numHashes P.length (p1StableProb 2 (2 * 1))) =>
          (Measure.pi fun _ : Fin 2 => cauchyMeasure 0 1).prod (uniformInterval 2)).real
        {s | query (andHash (p1StableHash 2) (numHashes P.length (p1StableProb 2 (2 * 1))))
          (fun x y => 2 * 1 ≤ ∑ i, |x i - y i|) s
          (3 * numTables P.length (p1StableProb 2 1) (p1StableProb 2 (2 * 1)))
          P ![0, 0] = none} ≤
      Real.exp (-1) + 1 / 3 := by
  intro P
  exact measureReal_query_p1Stable_eq_none_le (w := 2) (d := 1) (c := 2)
    (by norm_num) one_pos one_lt_two (P := P) (q := ![0, 0]) (x₀ := ![0, 0]) List.mem_cons_self
    (by simp only [sub_self, abs_zero, Finset.sum_const_zero, zero_le_one])

end CslibFrontierTests.LSHContinuous
