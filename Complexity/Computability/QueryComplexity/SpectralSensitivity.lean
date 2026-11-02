/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.QueryComplexity.Huang
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Complexity.Foundations.Data.BitString.Flip

/-!
# Spectral sensitivity

The *sensitivity graph* `G_f` of a Boolean function `f` is the subgraph of the cube whose edges join
neighbors `x` and `x ⊕ eᵢ` with `f(x) ≠ f(x ⊕ eᵢ)` (`BitString.sensitivityGraph`). The
*spectral sensitivity* `λ(f)` is the spectral norm of its adjacency matrix `A_f`, the operator norm
on `ℓ²` of the cube (`BitString.spectralSensitivity`) [AaronsonBenDavidKothariRaoTal2021]. A
vertex of `G_f` has as many neighbors as `f` has sensitive coordinates there, so `λ(f) ≤ s(f)`
(`BitString.spectralSensitivity_le_sensitivity`).

Huang's proof of the sensitivity theorem shows `deg(f) ≤ λ(f)²`
(`QueryComplexity.degree_le_spectralSensitivity_sq`). A Fourier coefficient on a set `S` of
`deg(f)` coordinates gives a set `V` of more than half of the points in which every edge in a
direction of `S` is sensitive (`BitString.exists_two_pow_lt_two_mul_card_forall_isSensitiveCoord`).
Huang's eigenvector bound (`BitString.exists_nonneg_ne_zero_sqrt_card_mul_le_sum`) gives a nonzero
nonnegative `v` with `√|S| v ≤ A_f v` pointwise, so `√deg(f) ‖v‖² ≤ ⟨v, A_f v⟩ ≤ λ(f) ‖v‖²`.

Two criteria bound `λ(f)` in terms of the bilinear form
`⟨u, A_f w⟩ = ∑_x ∑_{i sensitive at x} u(x) w(x ⊕ eᵢ)`: from below by a nonnegative `v` with
`c v ≤ A_f v` (`BitString.le_spectralSensitivity_of_le_sum`), and from above by its values at
nonnegative unit vectors (`BitString.spectralSensitivity_le_of_forall_sum_le`), since `A_f` has
nonnegative entries. The second is how the adversary bound
`Cslib.Quantum.one_sub_mul_spectralSensitivity_le` bounds `λ(f)` by quantum queries.

**Source mapping** (numbering of arXiv:2010.12629v1). `sensitivityGraph` and
`spectralSensitivity` are Definition 7. `spectralSensitivity_le_sensitivity` is the second step
of Huang's proof as stated in §3 ("the spectral norm of an adjacency matrix is at most the maximum
degree"), and `degree_le_spectralSensitivity_sq` is Theorem 1. The source restricts `f` to a
subcube of dimension `deg(f)` and applies Huang's signing of the whole subcube; here the signing
along the directions of `S` (`BitString.signedAdjacency`) avoids the restriction.

## Main definitions

* `Cslib.BitString.sensitivityGraph`: the sensitivity graph `G_f`.
* `Cslib.BitString.spectralSensitivity`: the spectral sensitivity `λ(f) = ‖A_f‖`.

## Main results

* `Cslib.BitString.adjMatrix_sensitivityGraph_mulVec_apply`: `(A_f v)(x)` sums `v` over the
  neighbors of `x` across sensitive coordinates.
* `Cslib.BitString.inner_toEuclideanCLM_adjMatrix_sensitivityGraph`: the bilinear form
  `⟨u, A_f v⟩ = ∑_x ∑_{i sensitive at x} u(x) v(x ⊕ eᵢ)`.
* `Cslib.BitString.le_spectralSensitivity_of_le_sum`,
  `Cslib.BitString.spectralSensitivity_le_of_forall_sum_le`: lower and upper criteria for `λ(f)`.
* `Cslib.BitString.spectralSensitivity_le_sensitivity`: `λ(f) ≤ s(f)`.
* `Cslib.QueryComplexity.degree_le_spectralSensitivity_sq`: `deg(f) ≤ λ(f)²`.

## References

* [S. Aaronson, S. Ben-David, R. Kothari, S. Rao, A. Tal, *Degree vs. approximate degree and
  quantum implications of Huang's sensitivity theorem*][AaronsonBenDavidKothariRaoTal2021]
* [H. Huang, *Induced subgraphs of hypercubes and a proof of the Sensitivity
  Conjecture*][Huang2019]
-/

public section

namespace Cslib

open Finset Function
open scoped Matrix

variable {n : ℕ}

namespace BitString

/-- A coordinate `i` is sensitive at `x` exactly when it is sensitive at `x ⊕ eᵢ`, the other end
of the edge. -/
theorem isSensitiveCoord_update_not_iff {f : BooleanFunction n} {x : BitString n} {i : Fin n} :
    IsSensitiveCoord f (update x i (!x i)) i ↔ IsSensitiveCoord f x i := by
  simp only [IsSensitiveCoord, update_self, Bool.not_not, update_idem, update_eq_self]
  exact ne_comm

/-- **Summing over the sensitive edges from either end**: each edge of the sensitivity graph in
direction `i` is counted once from each of its ends. -/
theorem sum_sum_sensitiveCoords_update {M : Type*} [AddCommMonoid M] (f : BooleanFunction n)
    (g : Fin n → BitString n → M) :
    ∑ x, ∑ i ∈ sensitiveCoords f x, g i (update x i (!x i)) =
      ∑ x, ∑ i ∈ sensitiveCoords f x, g i x := by
  simp only [sensitiveCoords, sum_filter]
  rw [sum_comm, sum_comm (f := fun x i => if IsSensitiveCoord f x i then g i x else 0)]
  refine sum_congr rfl fun i _ => ?_
  refine Fintype.sum_equiv (flipOn_involutive ({i} : Finset (Fin n))).toPerm _ _ fun x => ?_
  simp only [Involutive.coe_toPerm, flipOn_singleton, isSensitiveCoord_update_not_iff]

/-- The **sensitivity graph** `G_f` of `f` [AaronsonBenDavidKothariRaoTal2021]: the subgraph of
the cube joining `x` and `x ⊕ eᵢ` when `i` is sensitive for `f` at `x`, that is, when
`f(x) ≠ f(x ⊕ eᵢ)`. -/
def sensitivityGraph (f : BooleanFunction n) : SimpleGraph (BitString n) where
  Adj x y := ∃ i, IsSensitiveCoord f x i ∧ update x i (!x i) = y
  symm := ⟨by
    rintro x y ⟨i, hi, rfl⟩
    exact ⟨i, isSensitiveCoord_update_not_iff.2 hi, by
      simp only [update_self, Bool.not_not, update_idem, update_eq_self]⟩⟩
  loopless := ⟨by
    rintro x ⟨i, -, h⟩
    have := congrFun h i
    simp only [update_self] at this
    cases x i <;> simp at this⟩

/-- `x` and `y` are adjacent in the sensitivity graph when `y = x ⊕ eᵢ` for a coordinate `i`
sensitive at `x`. -/
theorem sensitivityGraph_adj {f : BooleanFunction n} {x y : BitString n} :
    (sensitivityGraph f).Adj x y ↔ ∃ i, IsSensitiveCoord f x i ∧ update x i (!x i) = y :=
  Iff.rfl

/-- Adjacency in the sensitivity graph is decidable. -/
instance (f : BooleanFunction n) : DecidableRel (sensitivityGraph f).Adj := fun x y =>
  inferInstanceAs (Decidable (∃ i, IsSensitiveCoord f x i ∧ update x i (!x i) = y))

/-- The neighbors of `x` in the sensitivity graph are its neighbors across sensitive
coordinates. -/
theorem neighborFinset_sensitivityGraph (f : BooleanFunction n) (x : BitString n) :
    (sensitivityGraph f).neighborFinset x =
      (sensitiveCoords f x).image fun i => update x i (!x i) := by
  ext y
  simp [sensitivityGraph_adj]

/-- The adjacency matrix of the sensitivity graph sums over the neighbors across sensitive
coordinates: `(A_f v)(x) = ∑_{i sensitive at x} v(x ⊕ eᵢ)`. -/
theorem adjMatrix_sensitivityGraph_mulVec_apply (f : BooleanFunction n) (v : BitString n → ℝ)
    (x : BitString n) :
    ((sensitivityGraph f).adjMatrix ℝ *ᵥ v) x =
      ∑ i ∈ sensitiveCoords f x, v (update x i (!x i)) := by
  rw [SimpleGraph.adjMatrix_mulVec_apply, neighborFinset_sensitivityGraph,
    sum_image fun i _ j _ h => update_not_injective x h]

/-- The **spectral sensitivity** `λ(f)` [AaronsonBenDavidKothariRaoTal2021]: the spectral norm of
the adjacency matrix `A_f` of the sensitivity graph, its operator norm on the Euclidean space of
real functions on the cube. By `Matrix.l2_opNorm_toEuclideanCLM` it is the norm of `A_f` for the
scoped `ℓ²` operator norm on matrices (`Matrix.Norms.L2Operator`). -/
noncomputable def spectralSensitivity (f : BooleanFunction n) : ℝ :=
  ‖Matrix.toEuclideanCLM (𝕜 := ℝ) ((sensitivityGraph f).adjMatrix ℝ)‖

/-- Spectral sensitivity is nonnegative. -/
theorem spectralSensitivity_nonneg (f : BooleanFunction n) : 0 ≤ spectralSensitivity f :=
  norm_nonneg _

open scoped RealInnerProductSpace in
/-- **The bilinear form of `A_f`**: `⟨u, A_f v⟩ = ∑_x ∑_{i sensitive at x} u(x) v(x ⊕ eᵢ)`. -/
theorem inner_toEuclideanCLM_adjMatrix_sensitivityGraph (f : BooleanFunction n)
    (u v : BitString n → ℝ) :
    ⟪WithLp.toLp 2 u, Matrix.toEuclideanCLM (𝕜 := ℝ) ((sensitivityGraph f).adjMatrix ℝ)
      (WithLp.toLp 2 v)⟫ =
      ∑ x, ∑ i ∈ sensitiveCoords f x, u x * v (update x i (!x i)) := by
  rw [Matrix.inner_toEuclideanCLM]
  simp only [dotProduct, adjMatrix_sensitivityGraph_mulVec_apply, mul_sum]

private theorem norm_toLp_sq (v : BitString n → ℝ) :
    ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (BitString n))‖ ^ 2 = ∑ x, v x ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]

/-- **Lower criterion**: a nonzero nonnegative `v` with `c v(x) ≤ (A_f v)(x)` at every point
witnesses `c ≤ λ(f)`. -/
theorem le_spectralSensitivity_of_le_sum {f : BooleanFunction n} {v : BitString n → ℝ} {c : ℝ}
    (hv : 0 ≤ v) (hv0 : v ≠ 0)
    (h : ∀ x, c * v x ≤ ∑ i ∈ sensitiveCoords f x, v (update x i (!x i))) :
    c ≤ spectralSensitivity f := by
  set A := Matrix.toEuclideanCLM (𝕜 := ℝ) ((sensitivityGraph f).adjMatrix ℝ)
  set w : EuclideanSpace ℝ (BitString n) := WithLp.toLp 2 v
  have hw : 0 < ‖w‖ := norm_pos_iff.2 fun h0 => hv0 (congrArg WithLp.ofLp h0)
  have h₁ : c * ‖w‖ ^ 2 ≤ inner ℝ w (A w) := by
    rw [norm_toLp_sq, inner_toEuclideanCLM_adjMatrix_sensitivityGraph, mul_sum]
    refine sum_le_sum fun x _ => ?_
    rw [← mul_sum]
    have hx : 0 ≤ v x := hv x
    nlinarith [mul_nonneg hx (sub_nonneg.2 (h x))]
  have h₂ : inner ℝ w (A w) ≤ ‖A‖ * ‖w‖ ^ 2 := by
    refine (real_inner_le_norm _ _).trans ?_
    have := A.le_opNorm w
    nlinarith [norm_nonneg w]
  exact le_of_mul_le_mul_right (h₁.trans h₂) (pow_pos hw 2)

/-- **Upper criterion**: `λ(f) ≤ K` if `⟨u, A_f w⟩ ≤ K` for all nonnegative unit vectors `u`
and `w`. Since `A_f` has nonnegative entries, replacing a pair of unit vectors by their absolute
values does not decrease the form. -/
theorem spectralSensitivity_le_of_forall_sum_le {f : BooleanFunction n} {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ u w : BitString n → ℝ, 0 ≤ u → 0 ≤ w → ∑ x, u x ^ 2 = 1 → ∑ x, w x ^ 2 = 1 →
      ∑ x, ∑ i ∈ sensitiveCoords f x, u x * w (update x i (!x i)) ≤ K) :
    spectralSensitivity f ≤ K := by
  refine ContinuousLinearMap.opNorm_le_bound _ hK fun z => ?_
  set A := Matrix.toEuclideanCLM (𝕜 := ℝ) ((sensitivityGraph f).adjMatrix ℝ)
  set y := A z
  set a := ‖y‖
  set b := ‖z‖
  rcases (norm_nonneg y).eq_or_lt with ha | ha
  · change ‖y‖ ≤ K * b
    rw [← ha]
    positivity
  rcases (norm_nonneg z).eq_or_lt with hb | hb
  · have hz : z = 0 := norm_eq_zero.1 hb.symm
    simp [y, hz] at ha
  -- `a² = ⟨y, A z⟩` is at most the form at the absolute values of `y` and `z`
  have hy : y = WithLp.toLp 2 y.ofLp := rfl
  have hz : z = WithLp.toLp 2 z.ofLp := rfl
  have h₁ : a ^ 2 ≤ ∑ x, ∑ i ∈ sensitiveCoords f x,
      |y.ofLp x| * |z.ofLp (update x i (!x i))| := by
    rw [← real_inner_self_eq_norm_sq]
    change inner ℝ y (A z) ≤ _
    rw [hy, hz, inner_toEuclideanCLM_adjMatrix_sensitivityGraph]
    refine sum_le_sum fun x _ => sum_le_sum fun i _ => ?_
    rw [← abs_mul]
    exact le_abs_self _
  -- the form at the normalized absolute values is at most `K`
  have hsq (v : EuclideanSpace ℝ (BitString n)) (hv : 0 < ‖v‖) :
      ∑ x, (|v.ofLp x| / ‖v‖) ^ 2 = 1 := by
    have := norm_toLp_sq v.ofLp
    simp only [div_pow, sq_abs, ← sum_div]
    rw [← this]
    exact div_self (pow_pos hv 2).ne'
  have h₂ := h (fun x => |y.ofLp x| / a) (fun x => |z.ofLp x| / b)
    (fun x => div_nonneg (abs_nonneg _) ha.le) (fun x => div_nonneg (abs_nonneg _) hb.le)
    (hsq y ha) (hsq z hb)
  have h₃ : ∑ x, ∑ i ∈ sensitiveCoords f x, |y.ofLp x| / a * (|z.ofLp (update x i (!x i))| / b) =
      (∑ x, ∑ i ∈ sensitiveCoords f x, |y.ofLp x| * |z.ofLp (update x i (!x i))|) / (a * b) := by
    simp only [sum_div, div_mul_div_comm]
  rw [h₃, div_le_iff₀ (mul_pos ha hb)] at h₂
  nlinarith

/-- **Spectral sensitivity is at most sensitivity**: `λ(f) ≤ s(f)`, the second step of Huang's
proof [AaronsonBenDavidKothariRaoTal2021]. By `2 u(x) w(y) ≤ u(x)² + w(y)²`, the form at unit
vectors is at most half the sum of `s_x(f) u(x)²` and `s_y(f) w(y)²` over the points. -/
theorem spectralSensitivity_le_sensitivity (f : BooleanFunction n) :
    spectralSensitivity f ≤ sensitivity f := by
  refine spectralSensitivity_le_of_forall_sum_le (Nat.cast_nonneg _) fun u w hu hw hu1 hw1 => ?_
  have hdeg (v : BitString n → ℝ) (hv1 : ∑ x, v x ^ 2 = 1) :
      ∑ x, ∑ _i ∈ sensitiveCoords f x, v x ^ 2 ≤ sensitivity f := by
    calc ∑ x, ∑ _i ∈ sensitiveCoords f x, v x ^ 2 = ∑ x, (sensitivityAt f x : ℝ) * v x ^ 2 := by
          simp [sum_const, sensitivityAt]
      _ ≤ ∑ x, (sensitivity f : ℝ) * v x ^ 2 := sum_le_sum fun x _ =>
          mul_le_mul_of_nonneg_right (Nat.cast_le.2 (sensitivityAt_le_sensitivity f x))
            (sq_nonneg _)
      _ = sensitivity f := by rw [← mul_sum, hv1, mul_one]
  have h₁ := hdeg u hu1
  have h₂ := hdeg w hw1
  rw [← sum_sum_sensitiveCoords_update f fun _ y => w y ^ 2] at h₂
  have h₃ : ∑ x, ∑ i ∈ sensitiveCoords f x, u x * w (update x i (!x i)) ≤
      (∑ x, ∑ _i ∈ sensitiveCoords f x, u x ^ 2 +
        ∑ x, ∑ i ∈ sensitiveCoords f x, w (update x i (!x i)) ^ 2) / 2 := by
    rw [← sum_add_distrib, sum_div]
    refine sum_le_sum fun x _ => ?_
    rw [← sum_add_distrib, sum_div]
    exact sum_le_sum fun i _ => by nlinarith [sq_nonneg (u x - w (update x i (!x i)))]
  linarith

end BitString

namespace QueryComplexity

open BitString

/-- **Huang's sensitivity theorem, spectral form**: the degree of a Boolean function is at most the
square of its spectral sensitivity, `deg(f) ≤ λ(f)²` [AaronsonBenDavidKothariRaoTal2021],
Theorem 1, from the proof of [Huang2019]. -/
theorem degree_le_spectralSensitivity_sq (f : BooleanFunction n) :
    (degree f : ℝ) ≤ spectralSensitivity f ^ 2 := by
  rcases Nat.eq_zero_or_pos (degree f) with h0 | hpos
  · rw [h0, Nat.cast_zero]
    positivity
  rw [degree_eq_totalDegree_signVal] at hpos ⊢
  obtain ⟨S, hS, hne⟩ := exists_card_eq_totalDegree_fourierCoeff_ne_zero hpos.ne'
  obtain ⟨V, hV, hsens⟩ := exists_two_pow_lt_two_mul_card_forall_isSensitiveCoord hne
  obtain ⟨v, hv, hv0, hvV, hvS⟩ := exists_nonneg_ne_zero_sqrt_card_mul_le_sum
    (by rwa [Fintype.card_fin]) S
  have h : √(#S : ℝ) ≤ spectralSensitivity f := by
    refine le_spectralSensitivity_of_le_sum hv hv0 fun x => ?_
    by_cases hx : x ∈ V
    · refine (hvS x).trans (sum_le_sum_of_subset_of_nonneg (fun i hi => ?_) fun i _ _ => hv _)
      obtain ⟨hiS, hiV⟩ := mem_filter.1 hi
      exact mem_sensitiveCoords.2 (hsens x hx i hiS hiV)
    · rw [hvV x hx, mul_zero]
      exact sum_nonneg fun i _ => hv _
  rw [← hS]
  calc (#S : ℝ) = √(#S : ℝ) ^ 2 := (Real.sq_sqrt (Nat.cast_nonneg _)).symm
    _ ≤ spectralSensitivity f ^ 2 :=
        pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2

end QueryComplexity

end Cslib
