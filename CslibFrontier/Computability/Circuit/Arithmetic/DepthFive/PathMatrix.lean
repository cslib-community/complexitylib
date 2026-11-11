/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.DepthFive.Path
public import CslibFrontier.Computability.Circuit.Arithmetic.DepthFive.RankMeasure
public import CslibFrontier.Computability.Circuit.Arithmetic.DepthFive.Schedule
import CslibFrontier.Computability.Circuit.Arithmetic.DepthFive.RankMeasureMap
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The matrix of the operator of iterated matrix multiplication

For the balanced layer schedule, the operator of `IMM_{n,n}` differentiates in the `k` edge
variables of a path that lie in differentiated layers and multiplies by the other `m`. On the
monomial `z ^ M` the summand of a path `P` therefore gives the monomial `z ^ N` with
`N + P.vPart = M + P.uPart`, with coefficient the product of the exponents `M e` over the
differentiated edges `e` of `P`. In the bases `z ^ M / √(M!)` the coefficient becomes the square
root of `Path.coeff`, the product of `M e` over the differentiated edges and of `M e + 1` over
the multiplied edges [OpenAI, §4][OpenAI2026DepthFive]. `pathMatrix` is this real matrix.

The matrix in the plain monomial bases has integer entries, so its rank is the same over every
field of characteristic zero, and the normalization rescales rows and columns by nonzero
numbers. Hence the rank of `pathMatrix` is the rank measure of `IMM_{n,n}` over every field of
characteristic zero [OpenAI, §6][OpenAI2026DepthFive].

## Main definitions

* `Cslib.Circuits.DepthFive.Slice`: the exponent vectors of a given bidegree.
* `Path.vPart`, `Path.uPart`: the differentiated and multiplied edges of a path.
* `Path.coeff`: the squared coefficient of a path in the normalized bases.
* `pathEntry`, `pathMatrix`: the matrix of the operator of `IMM_{n,n}` in the normalized bases.

## Main results

* `rank_pathMatrix_eq`: the rank of `pathMatrix` is the rank measure of `IMM_{n,n}`.

## References

* [OpenAI, *Homogeneous depth-five lower bounds for iterated matrix
  multiplication*][OpenAI2026DepthFive], §4 and §6 (unrefereed preprint)
-/

@[expose] public section

open MvPolynomial Finsupp Cslib.Circuits.Arithmetic

namespace Cslib.Circuits.DepthFive

variable (p : Params) [NeZero p.n]

/-- The exponent vectors of bidegree `d` for the variable split of the schedule. -/
abbrev Slice (p : Params) (d : ℕ × ℕ) :=
  {M : Fin p.n × Fin p.n × Fin p.n →₀ ℕ // weight (bidegWeight p.layerVar) M = d}

noncomputable instance (d : ℕ × ℕ) : Fintype (Slice p d) :=
  Fintype.ofEquiv _ (bidegreeEquiv p.layerVar d.1 d.2).symm

namespace Path

variable (P : Path p.n)

/-- The exponent vector of the edges of a path in the differentiated layers. -/
noncomputable def vPart : Fin p.n × Fin p.n × Fin p.n →₀ ℕ :=
  P.part (Finset.univ.filter fun t => p.isV t)

/-- The exponent vector of the edges of a path in the multiplied layers. -/
noncomputable def uPart : Fin p.n × Fin p.n × Fin p.n →₀ ℕ :=
  P.part (Finset.univ.filter fun t => ¬ p.isV t)

/-- The squared coefficient of a path at the exponent vector `M` in the normalized bases: the
product of `M e` over the differentiated edges and of `M e + 1` over the multiplied edges. -/
def coeff (M : Fin p.n × Fin p.n × Fin p.n →₀ ℕ) : ℕ :=
  ∏ t, if p.isV t then M (P.edge t) else M (P.edge t) + 1

theorem weight_part (T : Finset (Fin p.n)) :
    weight (bidegWeight p.layerVar) (P.part T) =
      ((T.filter fun t => p.isV t).card, (T.filter fun t => ¬ p.isV t).card) := by
  have h (t : Fin p.n) : bidegWeight p.layerVar (P.edge t) = if p.isV t then (1, 0) else (0, 1) :=
    rfl
  rw [part, map_sum, Finset.card_filter, Finset.card_filter]
  simp only [weight_single, one_smul, h]
  refine Prod.ext ?_ ?_
  · rw [Prod.fst_sum]
    exact Finset.sum_congr rfl fun t _ => by by_cases ht : p.isV t <;> simp [ht]
  · rw [Prod.snd_sum]
    exact Finset.sum_congr rfl fun t _ => by by_cases ht : p.isV t <;> simp [ht]

variable {p}

theorem weight_vPart (hcard : (Finset.univ.filter fun t => p.isV t).card = p.k) :
    weight (bidegWeight p.layerVar) (P.vPart p) = (p.k, 0) := by
  rw [vPart, weight_part, Finset.filter_filter, Finset.filter_filter]
  simp [hcard]

theorem weight_uPart (hcard : (Finset.univ.filter fun t => p.isV t).card = p.k) :
    weight (bidegWeight p.layerVar) (P.uPart p) = (0, p.m) := by
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin p.n)))
    (fun t => p.isV t)
  rw [hcard, Finset.card_univ, Fintype.card_fin] at h
  rw [uPart, weight_part, Finset.filter_filter, Finset.filter_filter]
  refine Prod.ext ?_ ?_
  · simp
  · have := p.hkm
    simp only [and_self]
    omega

theorem coeff_eq_mul (M : Fin p.n × Fin p.n × Fin p.n →₀ ℕ) :
    P.coeff p M = (∏ t with p.isV t, M (P.edge t)) * ∏ t with ¬ p.isV t, (M (P.edge t) + 1) := by
  rw [coeff, ← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun t => (p.isV t : Prop))]
  congr 1 <;> refine Finset.prod_congr rfl fun t ht => ?_
  · rw [ite_eq_left (Finset.mem_filter.1 ht).2]
  · rw [ite_eq_right (Finset.mem_filter.1 ht).2]

/-- If no differentiated edge of the path has exponent zero in `M`, the path can be
differentiated out of `M`. -/
theorem vPart_le {M : Fin p.n × Fin p.n × Fin p.n →₀ ℕ}
    (h : ∏ t with p.isV t, M (P.edge t) ≠ 0) : P.vPart p ≤ M := fun x => by
  rw [vPart, part_apply]
  split_ifs with hx
  · rw [← hx.2]
    exact Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.1 h _ hx.1)
  · exact Nat.zero_le _

/-- The bidegree of the image of a monomial under the summand of a path. -/
theorem weight_of_add_vPart_eq (hcard : (Finset.univ.filter fun t => p.isV t).card = p.k)
    {N M : Fin p.n × Fin p.n × Fin p.n →₀ ℕ} {a b : ℕ} (h : N + P.vPart p = M + P.uPart p)
    (hM : weight (bidegWeight p.layerVar) M = (a, b)) :
    weight (bidegWeight p.layerVar) N = (a - p.k, b + p.m) := by
  have h' := congrArg (weight (bidegWeight p.layerVar)) h
  rw [map_add, map_add, P.weight_vPart hcard, P.weight_uPart hcard, hM] at h'
  have h₁ := congrArg Prod.fst h'
  have h₂ := congrArg Prod.snd h'
  simp only [Prod.fst_add, Prod.snd_add, add_zero] at h₁ h₂
  exact Prod.ext (by change _ = a - p.k; omega) h₂

end Path

/-- The entry of the operator of `IMM_{n,n}` in the normalized monomial bases, between the
exponent vectors `M` and `N`. -/
noncomputable def pathEntry (N M : Fin p.n × Fin p.n × Fin p.n →₀ ℕ) : ℝ :=
  ∑ P : Path p.n, if N + P.vPart p = M + P.uPart p then √(P.coeff p M) else 0

/-- The matrix of the operator of `IMM_{n,n}` on the slice of bidegree `(a, b)`, in the
normalized monomial bases `z ^ M / √(M!)`. -/
noncomputable def pathMatrix : Matrix (Slice p (p.a - p.k, p.b + p.m)) (Slice p (p.a, p.b)) ℝ :=
  Matrix.of fun N M => pathEntry p N.1 M.1

variable {p}

/-- `IMM_{n,n}` has bidegree `(k, m)`. -/
theorem isWeightedHomogeneous_imm (K : Type*) [CommSemiring K]
    (hcard : (Finset.univ.filter fun t => p.isV t).card = p.k) :
    (imm K p.n p.n).IsWeightedHomogeneous (bidegWeight p.layerVar) (p.k, p.m) := by
  rw [imm_eq_sum_paths]
  refine IsWeightedHomogeneous.sum _ _ _ fun P _ => ?_
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun t => (p.isV t : Prop)),
    ← Path.monomial_part, ← Path.monomial_part]
  have h := (isWeightedHomogeneous_monomial (R := K) _ _ 1 (P.weight_vPart hcard)).mul
    (isWeightedHomogeneous_monomial (R := K) _ _ 1 (P.weight_uPart hcard))
  rw [show (p.k, p.m) = ((p.k, 0) + (0, p.m) : ℕ × ℕ) by simp]
  exact h

/-- The operator of the monomial of a path maps a monomial to a monomial. -/
private theorem mixedOp_path (P : Path p.n) (M : Fin p.n × Fin p.n × Fin p.n →₀ ℕ) :
    mixedOp p.layerVar (∏ t, X (P.edge t)) (monomial M (1 : ℝ)) =
      monomial (M - P.vPart p + P.uPart p)
        ((∏ t with p.isV t, M (P.edge t) : ℕ) : ℝ) := by
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun t => (p.isV t : Prop)), mul_comm,
    map_mul, Module.End.mul_apply,
    mixedOp_prod_X_monomial_of_pos p.layerVar (Finset.univ.filter fun t => p.isV t) P.edge
      (fun t ht => (Finset.mem_filter.1 ht).2) P.edge_injective.injOn,
    mixedOp_prod_X_of_neg p.layerVar (Finset.univ.filter fun t => ¬ p.isV t) P.edge
      (fun t ht => (Finset.mem_filter.1 ht).2), ← Path.monomial_part,
    monomial_mul_monomial, one_mul, one_mul, add_comm, Nat.cast_prod]
  rfl

/-- The factorial `M!` of an exponent vector. -/
private def fact (M : Fin p.n × Fin p.n × Fin p.n →₀ ℕ) : ℕ := ∏ x, (M x).factorial

private theorem fact_add_part (P : Path p.n) (T : Finset (Fin p.n))
    (M : Fin p.n × Fin p.n × Fin p.n →₀ ℕ) :
    fact (M + P.part T) = fact M * ∏ t ∈ T, (M (P.edge t) + 1) := by
  have h (x : Fin p.n × Fin p.n × Fin p.n) : ((M + P.part T) x).factorial =
      (M x).factorial * if x ∈ T.image P.edge then M x + 1 else 1 := by
    have hx : x ∈ T.image P.edge ↔ x.1 ∈ T ∧ P.edge x.1 = x :=
      ⟨fun h => by obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 h; exact ⟨ht, rfl⟩,
        fun h => Finset.mem_image.2 ⟨_, h⟩⟩
    rw [Finsupp.add_apply, Path.part_apply]
    simp only [hx]
    split_ifs
    · rw [Nat.factorial_succ, mul_comm]
    · rw [add_zero, mul_one]
  simp only [fact, h]
  rw [Finset.prod_mul_distrib, Finset.prod_ite_mem, Finset.univ_inter,
    Finset.prod_image P.edge_injective.injOn]

/-- The entry of a path in the normalized bases is its entry in the monomial bases, rescaled. -/
private theorem sqrt_fact_mul (P : Path p.n) (N M : Fin p.n × Fin p.n × Fin p.n →₀ ℕ) :
    √(fact N) * (monomial (M - P.vPart p + P.uPart p)
        ((∏ t with p.isV t, M (P.edge t) : ℕ) : ℝ)).coeff N * (√(fact M))⁻¹ =
      if N + P.vPart p = M + P.uPart p then √(P.coeff p M) else 0 := by
  have hc := P.coeff_eq_mul M
  rw [coeff_monomial]
  by_cases h0 : ∏ t with p.isV t, M (P.edge t) = 0
  · simp [hc, h0]
  have hle := P.vPart_le h0
  have hiff : M - P.vPart p + P.uPart p = N ↔ N + P.vPart p = M + P.uPart p := by
    rw [eq_comm, ← add_left_inj (P.vPart p), add_right_comm, tsub_add_cancel_of_le hle]
  simp only [hiff]
  split_ifs with h
  swap
  · simp
  have hV : ∏ t with p.isV t, (N (P.edge t) + 1) = ∏ t with p.isV t, M (P.edge t) := by
    refine Finset.prod_congr rfl fun t ht => ?_
    have := DFunLike.congr_fun h (P.edge t)
    simp only [Finsupp.add_apply, Path.vPart, Path.uPart, Path.part_apply, Path.edge_fst, ht,
      true_and, ite_true] at this
    simpa [(Finset.mem_filter.1 ht).2] using this
  have hfact : (fact N : ℝ) * (∏ t with p.isV t, M (P.edge t) : ℕ) =
      fact M * (∏ t with ¬ p.isV t, (M (P.edge t) + 1) : ℕ) := by
    rw [← hV]
    exact_mod_cast (fact_add_part P _ N).symm.trans ((congrArg fact h).trans (fact_add_part P _ M))
  have hM : (0 : ℝ) < fact M := by
    exact_mod_cast Finset.prod_pos fun x _ => Nat.factorial_pos _
  rw [← div_eq_mul_inv, div_eq_iff (Real.sqrt_pos.2 hM).ne', hc, Nat.cast_mul,
    ← Real.sqrt_mul (by positivity), mul_assoc, mul_comm _ (fact M : ℝ), ← hfact,
    ← Real.sqrt_sq (Nat.cast_nonneg (∏ t with p.isV t, M (P.edge t))),
    ← Real.sqrt_mul (Nat.cast_nonneg _)]
  congr 1
  rw [Real.sqrt_sq (Nat.cast_nonneg _)]
  ring

/-- The rank of the normalized matrix on the slice of bidegree `(a' + k, b)` is the rank measure
of `IMM_{n,n}` over the reals. -/
private theorem rank_of_pathEntry (hcard : (Finset.univ.filter fun t => p.isV t).card = p.k)
    (a' b : ℕ) : (Matrix.of fun (N : Slice p (a', b + p.m)) (M : Slice p (a' + p.k, b)) =>
        pathEntry p N.1 M.1).rank =
      rankMeasure p.layerVar (p.k, p.m) (a' + p.k, b) (imm ℝ p.n p.n) := by
  classical
  have hentry : (Matrix.of fun (N : Slice p (a', b + p.m)) (M : Slice p (a' + p.k, b)) =>
      pathEntry p N.1 M.1) = Matrix.diagonal (fun N : Slice p (a', b + p.m) => √(fact N.1)) *
        sliceMatrix (bidegWeight p.layerVar) (a', b + p.m) (a' + p.k, b)
          (mixedOp p.layerVar (imm ℝ p.n p.n)) *
        Matrix.diagonal (fun M : Slice p (a' + p.k, b) => (√(fact M.1))⁻¹) := by
    ext N M
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply, sliceMatrix, Matrix.of_apply,
      imm_eq_sum_paths, map_sum, LinearMap.sum_apply, coeff_sum, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun P _ => by rw [mixedOp_path, sqrt_fact_mul]
  have hpos (M : Fin p.n × Fin p.n × Fin p.n →₀ ℕ) : (0 : ℝ) < √(fact M) :=
    Real.sqrt_pos.2 (by exact_mod_cast Finset.prod_pos fun x _ => Nat.factorial_pos _)
  rw [hentry, Matrix.rank_mul_eq_left_of_isUnit_det, Matrix.rank_mul_eq_right_of_isUnit_det,
    rankMeasure_eq_rank_sliceMatrix,
    (isWeightedHomogeneous_imm ℝ hcard).weightedHomogeneousComponent_same]
  · rw [Matrix.det_diagonal]
    exact (Finset.prod_ne_zero_iff.2 fun N _ => (hpos N.1).ne').isUnit
  · rw [Matrix.det_diagonal]
    exact (Finset.prod_ne_zero_iff.2 fun M _ => (inv_pos.2 (hpos M.1)).ne').isUnit

/-- **The field transfer.** The rank of the real matrix `pathMatrix` is the rank measure of
`IMM_{n,n}` over every field of characteristic zero. -/
theorem rank_pathMatrix_eq (K : Type*) [Field K] [CharZero K]
    (hcard : (Finset.univ.filter fun t => p.isV t).card = p.k) (hka : p.k ≤ p.a) :
    (pathMatrix p).rank =
      rankMeasure p.layerVar (p.k, p.m) (p.a, p.b) (imm K p.n p.n) := by
  have h : ∀ a₀, a₀ = p.a - p.k + p.k →
      (Matrix.of fun (N : Slice p (p.a - p.k, p.b + p.m)) (M : Slice p (a₀, p.b)) =>
        pathEntry p N.1 M.1).rank =
      rankMeasure p.layerVar (p.k, p.m) (a₀, p.b) (imm K p.n p.n) := by
    rintro _ rfl
    rw [rank_of_pathEntry hcard, ← map_imm (Rat.castHom K), ← map_imm (Rat.castHom ℝ),
      rankMeasure_map, rankMeasure_map]
  exact h p.a (Nat.sub_add_cancel hka).symm

end Cslib.Circuits.DepthFive
