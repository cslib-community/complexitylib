/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.Quantum.WeightedAdversary
public import CslibFrontier.Computability.QueryComplexity.SpectralSensitivity
public import CslibFrontier.Foundations.Quantum.Measurement.Overlap
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.LinearAlgebra.Matrix.Hadamard
import CslibFrontier.Foundations.LinearAlgebra.Matrix.EuclideanOpNorm
import CslibFrontier.Foundations.Quantum.Measurement.Restrict

/-!
# Spectral and negative-weight quantum adversary bounds

This module develops the spectral adversary (`Cslib.Quantum.spectralAdversary`, denoted `ADV`) and
general negative-weight adversary (`Cslib.Quantum.generalAdversary`, denoted `ADV±`) bounds on
quantum query complexity, together with their bridges to sensitivity and weighted adversary
schemes:

* **Negative-weight adversary bound** [HoyerLeeSpalek2007], Theorem 2: for any real symmetric
  matrix `Γ` supported on `{(x, y) | P x ∧ P y ∧ f x ≠ f y}`, a `T`-query algorithm computing `f`
  on `P` with error at most `ε ≤ 1/2` satisfies
  `(1 - 2√(ε(1-ε))) ‖Γ‖ ≤ 2 T · maxDiffNorm Γ` for Boolean functions
  (`Cslib.Quantum.one_sub_mul_opNorm_le_general_boolean`), and
  `(1 - 2√(ε(1-ε)) - ε) ‖Γ‖ ≤ 2 T · maxDiffNorm Γ` (hence also with `- 2ε`) for arbitrary finite
  output alphabets (`Cslib.Quantum.one_sub_mul_opNorm_le_general`).
* **Nonnegative spectral adversary bound** [BarnumSaksSzegedy2003] (as reviewed in
  [HoyerLeeSpalek2007], Section 1.1, Theorem 1): when `0 ≤ Γ`, the nonnegative sign structure gives
  `(1 - δ) ‖Γ‖ ≤ 2 T · maxDiffNorm Γ` for any uniform final-state overlap bound `δ`
  (`Cslib.Quantum.one_sub_mul_opNorm_le_spectral`).
* **Hierarchies and nonnegative barriers**:
  `Cslib.Quantum.spectralSensitivity_le_spectralAdversary` (`λ(f) ≤ ADV(f)`),
  `Cslib.Quantum.WeightScheme.le_spectralAdversary` (`Alb₃(f) ≤ ADV(f)`, original proof
  formalizing the equivalence), `Cslib.Quantum.spectralAdversary_le_generalAdversary`
  (`ADV(f) ≤ ADV±(f)`), and the Hamming-distance barrier
  `k · ‖Γ‖ ≤ N · maxDiffNorm Γ` for `0 ≤ Γ`
  (`Cslib.Quantum.spectralAdversary_le_div_of_hammingDist_ge`).

## Main definitions

* `Cslib.Quantum.diffMatrix`: the coordinate-disagreement matrix `Dᵢ[x, y] = 1` iff `xᵢ ≠ yᵢ`.
* `Cslib.Quantum.maxDiffNorm`: `max_{i < N} ‖Γ ∘ Dᵢ‖` (`0` when `N = 0`).
* `Cslib.Quantum.IsAdversaryMatrix`: support predicate `Γ[x, y] ≠ 0 → P x ∧ P y ∧ f x ≠ f y`.
* `Cslib.Quantum.spectralAdversary`: supremum of `‖Γ‖ / maxDiffNorm Γ` over nonnegative
  symmetric adversary matrices.
* `Cslib.Quantum.generalAdversary`: supremum of `‖Γ‖ / maxDiffNorm Γ` over all real symmetric
  adversary matrices.

## Main results

* `Cslib.Quantum.spectralAdversary_le_iff` and `Cslib.Quantum.generalAdversary_le_iff`:
  strict-`module` upper-bound characterizations of `ADV(f)` and `ADV±(f)`.
* `Cslib.Quantum.one_sub_mul_generalAdversary_le_boolean`: negative-weight lower bound for
  Boolean outputs.
* `Cslib.Quantum.one_sub_mul_generalAdversary_le` and
  `Cslib.Quantum.one_sub_mul_generalAdversary_le_hls`: negative-weight lower bounds for finite
  output alphabets.
* `Cslib.Quantum.one_sub_mul_spectralAdversary_le`: spectral adversary lower bound.
* `Cslib.Quantum.spectralSensitivity_le_spectralAdversary`,
  `Cslib.Quantum.WeightScheme.le_spectralAdversary`, and
  `Cslib.Quantum.spectralAdversary_le_generalAdversary`: method hierarchy.
* `Cslib.Quantum.spectralAdversary_le_div_of_hammingDist_ge`: Hamming-distance barrier on `ADV`.

## References

* [H. Barnum, M. Saks, M. Szegedy, *Quantum query complexity and semidefinite programming*]
  [BarnumSaksSzegedy2003] (definition and theorem reviewed in [HoyerLeeSpalek2007], Section 1.1)
* [P. Høyer, T. Lee, R. Špalek, *Negative weights make adversaries stronger*][HoyerLeeSpalek2007]
* [S. Zhang, *On the power of Ambainis lower bounds*][Zhang2005]
-/

public section

namespace Cslib.Quantum

open Finset Function Matrix
open scoped RealInnerProductSpace Matrix.Norms.L2Operator

variable {N : ℕ}

section Helpers

private theorem norm_identity_helper {κ ι : Type*} [Fintype κ] [Fintype ι]
    (u : EuclideanSpace ℝ κ) (φ : κ → EuclideanSpace ℂ ι)
    (coord : κ → ι × Bool → ℝ)
    (hcoord : ∀ x p, coord x p = if p.2 then ((φ x).ofLp p.1).im else ((φ x).ofLp p.1).re) :
    ∑ p : ι × Bool, ‖(WithLp.toLp 2 fun x => u.ofLp x * coord x p : EuclideanSpace ℝ κ)‖ ^ 2 =
      ∑ x, (u.ofLp x * ‖φ x‖) ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq]
  rw [sum_comm]
  refine sum_congr rfl fun x _ => ?_
  rw [Fintype.sum_prod_type, mul_pow, EuclideanSpace.norm_sq_eq, mul_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp [hcoord]; ring

/-- Vector-matrix-inner-product Cauchy–Schwarz bound:
`|∑ x y, M[x, y] u_x v_y Re⟨φ_x, ψ_y⟩| ≤ ‖M‖ √(∑ x u_x² ‖φ_x‖²) √(∑ y v_y² ‖ψ_y‖²)`. -/
private theorem abs_sum_mul_re_inner_le {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι]
    (M : Matrix κ κ ℝ) (u v : EuclideanSpace ℝ κ) (φ ψ : κ → EuclideanSpace ℂ ι) :
    |∑ x, ∑ y, M x y * u.ofLp x * v.ofLp y * RCLike.re (inner ℂ (φ x) (ψ y))| ≤
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) M‖ *
        √(∑ x, (u.ofLp x * ‖φ x‖) ^ 2) * √(∑ y, (v.ofLp y * ‖ψ y‖) ^ 2) := by
  let coord : κ → ι × Bool → ℝ := fun x p =>
    if p.2 then ((φ x).ofLp p.1).im else ((φ x).ofLp p.1).re
  let coordψ : κ → ι × Bool → ℝ := fun y p =>
    if p.2 then ((ψ y).ofLp p.1).im else ((ψ y).ofLp p.1).re
  have hre (x y : κ) : RCLike.re (inner ℂ (φ x) (ψ y)) =
      ∑ p : ι × Bool, coord x p * coordψ y p := by
    rw [PiLp.inner_apply, map_sum, Fintype.sum_prod_type]
    refine sum_congr rfl fun k _ => ?_
    change ((ψ y).ofLp k * star ((φ x).ofLp k)).re = _
    simp [coord, coordψ, Complex.mul_re]
    ring
  have hrewrite :
      (∑ x, ∑ y, M x y * u.ofLp x * v.ofLp y * RCLike.re (inner ℂ (φ x) (ψ y))) =
      ∑ p : ι × Bool, ∑ x, ∑ y,
        M x y * (u.ofLp x * coord x p) * (v.ofLp y * coordψ y p) := by
    simp only [hre, mul_sum]
    calc ∑ x, ∑ y, ∑ p : ι × Bool, M x y * u.ofLp x * v.ofLp y * (coord x p * coordψ y p)
        = ∑ x, ∑ p : ι × Bool, ∑ y, M x y * u.ofLp x * v.ofLp y * (coord x p * coordψ y p) :=
          sum_congr rfl fun x _ => Finset.sum_comm
      _ = ∑ p : ι × Bool, ∑ x, ∑ y, M x y * u.ofLp x * v.ofLp y * (coord x p * coordψ y p) :=
          Finset.sum_comm
      _ = ∑ p : ι × Bool, ∑ x, ∑ y,
            M x y * (u.ofLp x * coord x p) * (v.ofLp y * coordψ y p) := by
          refine sum_congr rfl fun p _ => sum_congr rfl fun x _ => sum_congr rfl fun y _ => by ring
  let vecφ : ι × Bool → EuclideanSpace ℝ κ := fun p => WithLp.toLp 2 fun x => u.ofLp x * coord x p
  let vecψ : ι × Bool → EuclideanSpace ℝ κ := fun p => WithLp.toLp 2 fun y => v.ofLp y * coordψ y p
  have hcoord (p : ι × Bool) :
      (∑ x, ∑ y, M x y * (u.ofLp x * coord x p) * (v.ofLp y * coordψ y p)) =
      inner ℝ (vecφ p) (Matrix.toEuclideanCLM (𝕜 := ℝ) M (vecψ p)) := by
    rw [Matrix.inner_toEuclideanCLM]
    simp only [dotProduct, Matrix.mulVec, mul_sum, vecφ, vecψ]
    refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => by ring
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt (univ : Finset (ι × Bool))
    (fun p => ‖vecφ p‖) (fun p => ‖vecψ p‖)
  have hnormφ : ∑ p : ι × Bool, ‖vecφ p‖ ^ 2 = ∑ x, (u.ofLp x * ‖φ x‖) ^ 2 :=
    norm_identity_helper u φ coord fun _ _ => rfl
  have hnormψ : ∑ p : ι × Bool, ‖vecψ p‖ ^ 2 = ∑ y, (v.ofLp y * ‖ψ y‖) ^ 2 :=
    norm_identity_helper v ψ coordψ fun _ _ => rfl
  calc |∑ x, ∑ y, M x y * u.ofLp x * v.ofLp y * RCLike.re (inner ℂ (φ x) (ψ y))|
      = |∑ p : ι × Bool, inner ℝ (vecφ p) (Matrix.toEuclideanCLM (𝕜 := ℝ) M (vecψ p))| := by
          rw [hrewrite]; simp only [hcoord]
    _ ≤ ∑ p : ι × Bool, |inner ℝ (vecφ p) (Matrix.toEuclideanCLM (𝕜 := ℝ) M (vecψ p))| :=
          abs_sum_le_sum_abs _ _
    _ ≤ ∑ p : ι × Bool, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) M‖ * (‖vecφ p‖ * ‖vecψ p‖) := by
          refine sum_le_sum fun p _ => ?_
          calc |inner ℝ (vecφ p) (Matrix.toEuclideanCLM (𝕜 := ℝ) M (vecψ p))|
              ≤ ‖vecφ p‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) M (vecψ p)‖ :=
                abs_real_inner_le_norm _ _
            _ ≤ ‖vecφ p‖ * (‖Matrix.toEuclideanCLM (𝕜 := ℝ) M‖ * ‖vecψ p‖) :=
                mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
            _ = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) M‖ * (‖vecφ p‖ * ‖vecψ p‖) := by ring
    _ = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) M‖ * ∑ p : ι × Bool, ‖vecφ p‖ * ‖vecψ p‖ :=
          (mul_sum _ _ _).symm
    _ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) M‖ *
          (√(∑ p : ι × Bool, ‖vecφ p‖ ^ 2) * √(∑ p : ι × Bool, ‖vecψ p‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hcs (norm_nonneg _)
    _ = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) M‖ *
          √(∑ x, (u.ofLp x * ‖φ x‖) ^ 2) * √(∑ y, (v.ofLp y * ‖ψ y‖) ^ 2) := by
          rw [hnormφ, hnormψ, mul_assoc]

/-- Algebraic bound maximizing `√((1 - p) q) + √(p (1 - q))` for `0 ≤ p, q ≤ ε ≤ 1/2`. -/
private theorem mul_add_mul_le_two_mul_sqrt {a b p q ε : ℝ}
    (hp0 : 0 ≤ p) (hq0 : 0 ≤ q) (hpε : p ≤ ε) (hqε : q ≤ ε) (hε : 2 * ε ≤ 1)
    (hap : a ^ 2 + p ≤ 1) (hbq : b ^ 2 + q ≤ 1) :
    a * √q + √p * b ≤ 2 * √(ε * (1 - ε)) := by
  have ha1 : a ≤ √(1 - p) := Real.le_sqrt_of_sq_le (by linarith)
  have hb1 : b ≤ √(1 - q) := Real.le_sqrt_of_sq_le (by linarith)
  have hsum : a * √q + √p * b ≤ √((1 - p) * q) + √(p * (1 - q)) := by
    rw [Real.sqrt_mul (by linarith), Real.sqrt_mul hp0]
    exact add_le_add (mul_le_mul_of_nonneg_right ha1 (Real.sqrt_nonneg _))
      (mul_le_mul_of_nonneg_left hb1 (Real.sqrt_nonneg _))
  have hε0 : 0 ≤ ε := hp0.trans hpε
  have hε1 : 0 ≤ 1 - ε := by linarith
  have hp_bd : p * (1 - p) ≤ ε * (1 - ε) := by nlinarith
  have hq_bd : q * (1 - q) ≤ ε * (1 - ε) := by nlinarith
  have hmix : (1 - p) * q + p * (1 - q) ≤ 2 * (ε * (1 - ε)) := by nlinarith
  have hsq : (√((1 - p) * q) + √(p * (1 - q))) ^ 2 ≤ (2 * √(ε * (1 - ε))) ^ 2 := by
    have hprod : √((1 - p) * q) * √(p * (1 - q)) ≤ ε * (1 - ε) := by
      calc √((1 - p) * q) * √(p * (1 - q))
          = √(p * (1 - p) * (q * (1 - q))) := by
              rw [← Real.sqrt_mul (by nlinarith)]
              congr 1; ring
        _ ≤ √((ε * (1 - ε)) * (ε * (1 - ε))) :=
              Real.sqrt_le_sqrt (mul_le_mul hp_bd hq_bd (by nlinarith) (by nlinarith))
        _ = ε * (1 - ε) := Real.sqrt_mul_self (mul_nonneg hε0 hε1)
    calc (√((1 - p) * q) + √(p * (1 - q))) ^ 2
        = (1 - p) * q + p * (1 - q) + 2 * (√((1 - p) * q) * √(p * (1 - q))) := by
            rw [add_sq, Real.sq_sqrt (by nlinarith), Real.sq_sqrt (by nlinarith)]
            ring
      _ ≤ 2 * (ε * (1 - ε)) + 2 * (ε * (1 - ε)) := add_le_add hmix (by linarith)
      _ = (2 * √(ε * (1 - ε))) ^ 2 := by
            rw [mul_pow, Real.sq_sqrt (mul_nonneg hε0 hε1)]
            ring
  have hle : √((1 - p) * q) + √(p * (1 - q)) ≤ 2 * √(ε * (1 - ε)) := by
    nlinarith [Real.sqrt_nonneg ((1 - p) * q), Real.sqrt_nonneg (p * (1 - q)),
      Real.sqrt_nonneg (ε * (1 - ε))]
  exact hsum.trans hle

end Helpers

section Definitions

/-- Coordinate-disagreement matrix `Dᵢ`: entry `(x, y)` is `1` if `xᵢ ≠ yᵢ` and `0` otherwise. -/
@[expose] def diffMatrix (i : Fin N) : Matrix (BitString N) (BitString N) ℝ :=
  Matrix.of fun x y => if x i ≠ y i then 1 else 0

@[simp] theorem diffMatrix_apply (i : Fin N) (x y : BitString N) :
    diffMatrix i x y = if x i ≠ y i then 1 else 0 :=
  rfl

theorem diffMatrix_transpose (i : Fin N) : (diffMatrix i)ᵀ = diffMatrix i := by
  ext x y
  simp [ne_comm]

/-- Maximum coordinate-masked operator norm `max_{i < N} ‖Γ ∘ Dᵢ‖` (`0` when `N = 0`). -/
noncomputable def maxDiffNorm (Γ : Matrix (BitString N) (BitString N) ℝ) : ℝ :=
  (((univ : Finset (Fin N)).sup fun i =>
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (Γ.hadamard (diffMatrix i))‖₊ : NNReal) : ℝ)

theorem maxDiffNorm_nonneg (Γ : Matrix (BitString N) (BitString N) ℝ) : 0 ≤ maxDiffNorm Γ :=
  NNReal.coe_nonneg _

theorem norm_toEuclideanCLM_hadamard_le_maxDiffNorm
    (Γ : Matrix (BitString N) (BitString N) ℝ) (i : Fin N) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (Γ.hadamard (diffMatrix i))‖ ≤ maxDiffNorm Γ := by
  unfold maxDiffNorm
  exact NNReal.coe_le_coe.2 (Finset.le_sup (f := fun j =>
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (Γ.hadamard (diffMatrix j))‖₊) (mem_univ i))

theorem maxDiffNorm_le_iff {Γ : Matrix (BitString N) (BitString N) ℝ} {K : ℝ} (hK : 0 ≤ K) :
    maxDiffNorm Γ ≤ K ↔ ∀ i, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (Γ.hadamard (diffMatrix i))‖ ≤ K := by
  refine ⟨fun h i => (norm_toEuclideanCLM_hadamard_le_maxDiffNorm Γ i).trans h, fun h => ?_⟩
  unfold maxDiffNorm
  rw [← Real.coe_toNNReal K hK, NNReal.coe_le_coe, Finset.sup_le_iff]
  intro i _
  exact (Real.le_toNNReal_iff_coe_le hK).2 (h i)

/-- Support condition for an adversary matrix of a partial function `(P, f)`: every nonzero
entry `(x, y)` connects valid inputs with distinct outputs. -/
@[expose] def IsAdversaryMatrix {α : Type*} (P : BitString N → Prop) (f : BitString N → α)
    (Γ : Matrix (BitString N) (BitString N) ℝ) : Prop :=
  ∀ x y, Γ x y ≠ 0 → P x ∧ P y ∧ f x ≠ f y

theorem eq_zero_of_maxDiffNorm_eq_zero {α : Type*} {P : BitString N → Prop} {f : BitString N → α}
    {Γ : Matrix (BitString N) (BitString N) ℝ} (hΓ : IsAdversaryMatrix P f Γ)
    (h0 : maxDiffNorm Γ = 0) : Γ = 0 := by
  ext x y
  by_contra hne
  have hxy : x ≠ y := fun h => (hΓ x y hne).2.2 (congrArg f h)
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hxy
  have hle := Matrix.abs_entry_le_norm_toEuclideanCLM (Γ.hadamard (diffMatrix i)) x y
  have hmax := norm_toEuclideanCLM_hadamard_le_maxDiffNorm Γ i
  simp only [Matrix.hadamard_apply, diffMatrix_apply, hi, ne_eq, not_false_eq_true, ↓reduceIte,
    mul_one] at hle
  rw [h0] at hmax
  exact hne (abs_eq_zero.1 (le_antisymm (hle.trans hmax) (abs_nonneg _)))

/-- **Nonnegative spectral adversary bound `ADV(f)`** ([BarnumSaksSzegedy2003], as reviewed in
[HoyerLeeSpalek2007], Section 1.1, Definition 1): the supremum of `‖Γ‖ / maxDiffNorm Γ` over real
symmetric nonnegative matrices supported on pairs `(x, y)` with `P x`, `P y`, and `f x ≠ f y`. -/
noncomputable def spectralAdversary {α : Type*} (P : BitString N → Prop) (f : BitString N → α) :
    ℝ :=
  sSup {r : ℝ | ∃ Γ : Matrix (BitString N) (BitString N) ℝ,
    Γ.IsSymm ∧ (∀ x y, 0 ≤ Γ x y) ∧ IsAdversaryMatrix P f Γ ∧
      r = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ / maxDiffNorm Γ}

/-- **Negative-weight adversary bound `ADV±(f)`** ([HoyerLeeSpalek2007], Definition 2):
the supremum of `‖Γ‖ / maxDiffNorm Γ` over all real symmetric matrices supported on pairs
`(x, y)` with `P x`, `P y`, and `f x ≠ f y`. -/
noncomputable def generalAdversary {α : Type*} (P : BitString N → Prop) (f : BitString N → α) :
    ℝ :=
  sSup {r : ℝ | ∃ Γ : Matrix (BitString N) (BitString N) ℝ,
    Γ.IsSymm ∧ IsAdversaryMatrix P f Γ ∧
      r = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ / maxDiffNorm Γ}

private theorem norm_div_maxDiffNorm_le_card {α : Type*} {P : BitString N → Prop}
    {f : BitString N → α} {Γ : Matrix (BitString N) (BitString N) ℝ}
    (hΓ : IsAdversaryMatrix P f Γ) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ / maxDiffNorm Γ ≤ (Fintype.card (BitString N) : ℝ) := by
  by_cases h0 : maxDiffNorm Γ = 0
  · simp [h0]
  have hpos : 0 < maxDiffNorm Γ := lt_of_le_of_ne (maxDiffNorm_nonneg Γ) (Ne.symm h0)
  have hentry (x y : BitString N) : |Γ x y| ≤ maxDiffNorm Γ := by
    by_cases hxy0 : Γ x y = 0
    · simp [hxy0, maxDiffNorm_nonneg Γ]
    · have hxy : x ≠ y := fun h => (hΓ x y hxy0).2.2 (congrArg f h)
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hxy
      calc |Γ x y| = |(Γ.hadamard (diffMatrix i)) x y| := by simp [hi]
        _ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (Γ.hadamard (diffMatrix i))‖ :=
              Matrix.abs_entry_le_norm_toEuclideanCLM _ x y
        _ ≤ maxDiffNorm Γ := norm_toEuclideanCLM_hadamard_le_maxDiffNorm Γ i
  have hrow (x : BitString N) :
      ∑ y, |Γ x y| ≤ (Fintype.card (BitString N) : ℝ) * maxDiffNorm Γ := by
    calc ∑ y, |Γ x y| ≤ ∑ _y : BitString N, maxDiffNorm Γ := sum_le_sum fun y _ => hentry x y
      _ = (Fintype.card (BitString N) : ℝ) * maxDiffNorm Γ := by simp
  have hcol (y : BitString N) :
      ∑ x, |Γ x y| ≤ (Fintype.card (BitString N) : ℝ) * maxDiffNorm Γ := by
    calc ∑ x, |Γ x y| ≤ ∑ _x : BitString N, maxDiffNorm Γ := sum_le_sum fun x _ => hentry x y
      _ = (Fintype.card (BitString N) : ℝ) * maxDiffNorm Γ := by simp
  have hschur := Matrix.opNorm_toEuclideanCLM_le_sqrt Γ (by positivity) (by positivity) hrow hcol
  rw [Real.sqrt_mul_self (by positivity)] at hschur
  exact (div_le_iff₀ hpos).2 hschur

theorem bddAbove_generalAdversary {α : Type*} (P : BitString N → Prop) (f : BitString N → α) :
    BddAbove {r : ℝ | ∃ Γ : Matrix (BitString N) (BitString N) ℝ,
      Γ.IsSymm ∧ IsAdversaryMatrix P f Γ ∧
        r = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ / maxDiffNorm Γ} :=
  ⟨Fintype.card (BitString N), by
    rintro r ⟨Γ, -, hΓ, rfl⟩
    exact norm_div_maxDiffNorm_le_card hΓ⟩

theorem bddAbove_spectralAdversary {α : Type*} (P : BitString N → Prop) (f : BitString N → α) :
    BddAbove {r : ℝ | ∃ Γ : Matrix (BitString N) (BitString N) ℝ,
      Γ.IsSymm ∧ (∀ x y, 0 ≤ Γ x y) ∧ IsAdversaryMatrix P f Γ ∧
        r = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ / maxDiffNorm Γ} :=
  ⟨Fintype.card (BitString N), by
    rintro r ⟨Γ, -, -, hΓ, rfl⟩
    exact norm_div_maxDiffNorm_le_card hΓ⟩

theorem spectralAdversary_nonneg {α : Type*} (P : BitString N → Prop) (f : BitString N → α) :
    0 ≤ spectralAdversary P f := by
  refine le_csSup (bddAbove_spectralAdversary P f) ⟨0, Matrix.isSymm_zero, fun _ _ => le_rfl,
    fun _ _ h => (h rfl).elim, ?_⟩
  simp

theorem generalAdversary_nonneg {α : Type*} (P : BitString N → Prop) (f : BitString N → α) :
    0 ≤ generalAdversary P f := by
  refine le_csSup (bddAbove_generalAdversary P f) ⟨0, Matrix.isSymm_zero,
    fun _ _ h => (h rfl).elim, ?_⟩
  simp

theorem le_spectralAdversary {α : Type*} {P : BitString N → Prop} {f : BitString N → α}
    {Γ : Matrix (BitString N) (BitString N) ℝ} (hsym : Γ.IsSymm) (hnonneg : ∀ x y, 0 ≤ Γ x y)
    (hΓ : IsAdversaryMatrix P f Γ) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ / maxDiffNorm Γ ≤ spectralAdversary P f :=
  le_csSup (bddAbove_spectralAdversary P f) ⟨Γ, hsym, hnonneg, hΓ, rfl⟩

theorem le_generalAdversary {α : Type*} {P : BitString N → Prop} {f : BitString N → α}
    {Γ : Matrix (BitString N) (BitString N) ℝ} (hsym : Γ.IsSymm)
    (hΓ : IsAdversaryMatrix P f Γ) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ / maxDiffNorm Γ ≤ generalAdversary P f :=
  le_csSup (bddAbove_generalAdversary P f) ⟨Γ, hsym, hΓ, rfl⟩

private theorem div_maxDiffNorm_le_of_mul {Γ : Matrix (BitString N) (BitString N) ℝ}
    {K : ℝ} (hK : 0 ≤ K)
    (h : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ ≤ K * maxDiffNorm Γ) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ / maxDiffNorm Γ ≤ K := by
  by_cases hm0 : maxDiffNorm Γ = 0
  · simp [hm0, hK]
  · have hm : 0 < maxDiffNorm Γ := lt_of_le_of_ne (maxDiffNorm_nonneg Γ) (Ne.symm hm0)
    exact (div_le_iff₀ hm).2 h

private theorem mul_maxDiffNorm_of_div_le {α : Type*} {P : BitString N → Prop}
    {f : BitString N → α} {Γ : Matrix (BitString N) (BitString N) ℝ}
    (hΓ : IsAdversaryMatrix P f Γ) {K : ℝ}
    (h : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ / maxDiffNorm Γ ≤ K) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ ≤ K * maxDiffNorm Γ := by
  by_cases hm0 : maxDiffNorm Γ = 0
  · rw [hm0, mul_zero, eq_zero_of_maxDiffNorm_eq_zero hΓ hm0, map_zero, norm_zero]
  · have hm : 0 < maxDiffNorm Γ := lt_of_le_of_ne (maxDiffNorm_nonneg Γ) (Ne.symm hm0)
    exact (div_le_iff₀ hm).1 h

/-- Upper-bound characterization of `spectralAdversary` (`ADV(f) ≤ K` for `K ≥ 0`). -/
theorem spectralAdversary_le_iff {α : Type*} {P : BitString N → Prop} {f : BitString N → α}
    {K : ℝ} (hK : 0 ≤ K) :
    spectralAdversary P f ≤ K ↔
      ∀ Γ : Matrix (BitString N) (BitString N) ℝ, Γ.IsSymm → (∀ x y, 0 ≤ Γ x y) →
        IsAdversaryMatrix P f Γ → ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ ≤ K * maxDiffNorm Γ := by
  refine ⟨fun hle Γ hsym hnonneg hΓ =>
    mul_maxDiffNorm_of_div_le hΓ ((le_spectralAdversary hsym hnonneg hΓ).trans hle), fun h => ?_⟩
  refine csSup_le ⟨0, 0, Matrix.isSymm_zero, fun _ _ => le_rfl,
    fun _ _ h => (h rfl).elim, by simp⟩ ?_
  rintro r ⟨Γ, hsym, hnonneg, hΓ, rfl⟩
  exact div_maxDiffNorm_le_of_mul hK (h Γ hsym hnonneg hΓ)

/-- Upper-bound characterization of `generalAdversary` (`ADV±(f) ≤ K` for `K ≥ 0`). -/
theorem generalAdversary_le_iff {α : Type*} {P : BitString N → Prop} {f : BitString N → α}
    {K : ℝ} (hK : 0 ≤ K) :
    generalAdversary P f ≤ K ↔
      ∀ Γ : Matrix (BitString N) (BitString N) ℝ, Γ.IsSymm →
        IsAdversaryMatrix P f Γ → ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ ≤ K * maxDiffNorm Γ := by
  refine ⟨fun hle Γ hsym hΓ =>
    mul_maxDiffNorm_of_div_le hΓ ((le_generalAdversary hsym hΓ).trans hle), fun h => ?_⟩
  refine csSup_le ⟨0, 0, Matrix.isSymm_zero, fun _ _ h => (h rfl).elim, by simp⟩ ?_
  rintro r ⟨Γ, hsym, hΓ, rfl⟩
  exact div_maxDiffNorm_le_of_mul hK (h Γ hsym hΓ)

/-- `ADV(f) ≤ ADV±(f)`: the negative-weight adversary bound is at least the nonnegative spectral
adversary bound. -/
theorem spectralAdversary_le_generalAdversary {α : Type*} (P : BitString N → Prop)
    (f : BitString N → α) : spectralAdversary P f ≤ generalAdversary P f := by
  refine csSup_le ⟨0, 0, Matrix.isSymm_zero, fun _ _ => le_rfl,
    fun _ _ h => (h rfl).elim, by simp⟩ ?_
  rintro r ⟨Γ, hsym, -, hΓ, rfl⟩
  exact le_generalAdversary hsym hΓ

end Definitions

section ProgressCore

variable {W : Type*} [Fintype W]

/-- Bilinear adversary progress measure `W(φ) = ∑_{x,y} Γ[x, y] u_x v_y Re⟨φ_x, φ_y⟩`. -/
private noncomputable def advForm (Γ : Matrix (BitString N) (BitString N) ℝ)
    (u v : EuclideanSpace ℝ (BitString N)) (φ : BitString N → State N W) : ℝ :=
  ∑ x, ∑ y, Γ x y * u.ofLp x * v.ofLp y * RCLike.re (inner ℂ (φ x) (φ y))

private theorem advForm_step_sub_le (Γ : Matrix (BitString N) (BitString N) ℝ)
    (u v : EuclideanSpace ℝ (BitString N)) (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (U : ℕ → State N W →ₗᵢ[ℂ] State N W) {ψ₀ : State N W} (hψ₀ : ‖ψ₀‖ = 1) (t : ℕ) :
    |advForm Γ u v (fun x => run U ψ₀ x t) - advForm Γ u v (fun x => run U ψ₀ x (t + 1))| ≤
      2 * maxDiffNorm Γ := by
  have hdiff (x y : BitString N) :
      RCLike.re (inner ℂ (run U ψ₀ x t) (run U ψ₀ y t)) -
        RCLike.re (inner ℂ (run U ψ₀ x (t + 1)) (run U ψ₀ y (t + 1))) =
      2 * ∑ i : Fin N, (diffMatrix i x y) *
        RCLike.re (inner ℂ (ctrlProj i (run U ψ₀ x t)) (ctrlProj i (run U ψ₀ y t))) := by
    have hrun : inner ℂ (run U ψ₀ x (t + 1)) (run U ψ₀ y (t + 1)) =
        inner ℂ (phaseOracle x (run U ψ₀ x t)) (phaseOracle y (run U ψ₀ y t)) :=
      (U (t + 1)).inner_map_map _ _
    rw [hrun, inner_phaseOracle_phaseOracle, ← map_sub, sub_sub_cancel]
    have hre2 : ∀ z : ℂ, RCLike.re (2 * z) = 2 * RCLike.re z := fun z => by
      simp [RCLike.re, Complex.mul_re]
    rw [hre2, map_sum, Finset.sum_filter]
    congr 1
    refine sum_congr rfl fun i _ => ?_
    simp only [diffMatrix_apply, ne_eq]
    split_ifs <;> simp
  have hrewrite :
      advForm Γ u v (fun x => run U ψ₀ x t) - advForm Γ u v (fun x => run U ψ₀ x (t + 1)) =
      2 * ∑ i : Fin N, ∑ x, ∑ y,
        (Γ.hadamard (diffMatrix i)) x y * u.ofLp x * v.ofLp y *
          RCLike.re (inner ℂ (ctrlProj i (run U ψ₀ x t)) (ctrlProj i (run U ψ₀ y t))) := by
    simp only [advForm, ← sum_sub_distrib, ← mul_sub, hdiff]
    rw [mul_sum]
    have hxy (x y : BitString N) :
        Γ x y * u.ofLp x * v.ofLp y * (2 * ∑ i : Fin N,
          diffMatrix i x y * RCLike.re (inner ℂ (ctrlProj i (run U ψ₀ x t))
            (ctrlProj i (run U ψ₀ y t)))) =
        ∑ i : Fin N, 2 * ((Γ.hadamard (diffMatrix i)) x y * u.ofLp x * v.ofLp y *
          RCLike.re (inner ℂ (ctrlProj i (run U ψ₀ x t)) (ctrlProj i (run U ψ₀ y t)))) := by
      rw [mul_sum, mul_sum]
      refine sum_congr rfl fun i _ => by rw [Matrix.hadamard_apply]; ring
    simp_rw [hxy]
    calc ∑ x, ∑ y, ∑ i : Fin N, 2 * ((Γ.hadamard (diffMatrix i)) x y * u.ofLp x * v.ofLp y *
            RCLike.re (inner ℂ (ctrlProj i (run U ψ₀ x t)) (ctrlProj i (run U ψ₀ y t))))
        = ∑ x, ∑ i : Fin N, ∑ y, 2 * ((Γ.hadamard (diffMatrix i)) x y * u.ofLp x * v.ofLp y *
            RCLike.re (inner ℂ (ctrlProj i (run U ψ₀ x t)) (ctrlProj i (run U ψ₀ y t)))) :=
          sum_congr rfl fun x _ => Finset.sum_comm
      _ = ∑ i : Fin N, ∑ x, ∑ y, 2 * ((Γ.hadamard (diffMatrix i)) x y * u.ofLp x * v.ofLp y *
            RCLike.re (inner ℂ (ctrlProj i (run U ψ₀ x t)) (ctrlProj i (run U ψ₀ y t)))) :=
          Finset.sum_comm
      _ = ∑ i : Fin N, 2 * ∑ x, ∑ y, (Γ.hadamard (diffMatrix i)) x y * u.ofLp x * v.ofLp y *
            RCLike.re (inner ℂ (ctrlProj i (run U ψ₀ x t)) (ctrlProj i (run U ψ₀ y t))) := by
          refine sum_congr rfl fun i _ => ?_
          symm
          rw [mul_sum]
          exact sum_congr rfl fun x _ => mul_sum _ _ _
  rw [hrewrite, abs_mul, abs_of_nonneg zero_le_two]
  have hstep :
      |∑ i : Fin N, ∑ x, ∑ y,
        (Γ.hadamard (diffMatrix i)) x y * u.ofLp x * v.ofLp y *
          RCLike.re (inner ℂ (ctrlProj i (run U ψ₀ x t)) (ctrlProj i (run U ψ₀ y t)))| ≤
      maxDiffNorm Γ := by
    calc |∑ i : Fin N, ∑ x, ∑ y,
          (Γ.hadamard (diffMatrix i)) x y * u.ofLp x * v.ofLp y *
            RCLike.re (inner ℂ (ctrlProj i (run U ψ₀ x t)) (ctrlProj i (run U ψ₀ y t)))|
        ≤ ∑ i : Fin N, |∑ x, ∑ y,
            (Γ.hadamard (diffMatrix i)) x y * u.ofLp x * v.ofLp y *
              RCLike.re (inner ℂ (ctrlProj i (run U ψ₀ x t)) (ctrlProj i (run U ψ₀ y t)))| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin N, maxDiffNorm Γ *
            √(∑ x, (u.ofLp x * ‖ctrlProj i (run U ψ₀ x t)‖) ^ 2) *
            √(∑ y, (v.ofLp y * ‖ctrlProj i (run U ψ₀ y t)‖) ^ 2) := by
          refine sum_le_sum fun i _ => ?_
          have hb := abs_sum_mul_re_inner_le (Γ.hadamard (diffMatrix i)) u v
            (fun x => ctrlProj i (run U ψ₀ x t)) (fun y => ctrlProj i (run U ψ₀ y t))
          have hnorm := norm_toEuclideanCLM_hadamard_le_maxDiffNorm Γ i
          exact hb.trans (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hnorm (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
      _ = maxDiffNorm Γ * ∑ i : Fin N,
            √(∑ x, (u.ofLp x * ‖ctrlProj i (run U ψ₀ x t)‖) ^ 2) *
            √(∑ y, (v.ofLp y * ‖ctrlProj i (run U ψ₀ y t)‖) ^ 2) := by
          rw [mul_sum]
          refine sum_congr rfl fun i _ => by ring
      _ ≤ maxDiffNorm Γ *
            (√(∑ i : Fin N, ∑ x, (u.ofLp x * ‖ctrlProj i (run U ψ₀ x t)‖) ^ 2) *
             √(∑ i : Fin N, ∑ y, (v.ofLp y * ‖ctrlProj i (run U ψ₀ y t)‖) ^ 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ (maxDiffNorm_nonneg Γ)
          have hcs := Real.sum_mul_le_sqrt_mul_sqrt (univ : Finset (Fin N))
            (fun i => √(∑ x, (u.ofLp x * ‖ctrlProj i (run U ψ₀ x t)‖) ^ 2))
            (fun i => √(∑ y, (v.ofLp y * ‖ctrlProj i (run U ψ₀ y t)‖) ^ 2))
          simpa [Real.sq_sqrt (sum_nonneg fun _ _ => sq_nonneg _)] using hcs
      _ ≤ maxDiffNorm Γ * (1 * 1) := by
          refine mul_le_mul_of_nonneg_left ?_ (maxDiffNorm_nonneg Γ)
          have hctrl (w : EuclideanSpace ℝ (BitString N)) (hw : ‖w‖ ≤ 1) :
              √(∑ i : Fin N, ∑ x, (w.ofLp x * ‖ctrlProj i (run U ψ₀ x t)‖) ^ 2) ≤ 1 := by
            rw [Real.sqrt_le_one, sum_comm]
            calc ∑ x, ∑ i : Fin N, (w.ofLp x * ‖ctrlProj i (run U ψ₀ x t)‖) ^ 2
                = ∑ x, w.ofLp x ^ 2 * ∑ i : Fin N, ‖ctrlProj i (run U ψ₀ x t)‖ ^ 2 := by
                    refine sum_congr rfl fun x _ => ?_
                    rw [mul_sum]
                    refine sum_congr rfl fun i _ => by rw [mul_pow]
              _ ≤ ∑ x, w.ofLp x ^ 2 * 1 := sum_le_sum fun x _ =>
                    mul_le_mul_of_nonneg_left (sum_sq_norm_ctrlProj_le U hψ₀ x t) (sq_nonneg _)
              _ = ∑ x, w.ofLp x ^ 2 := by simp
              _ ≤ 1 := by
                    rw [← EuclideanSpace.real_norm_sq_eq]
                    exact pow_le_one₀ (norm_nonneg _) hw
          exact mul_le_mul (hctrl u hu) (hctrl v hv) (Real.sqrt_nonneg _) zero_le_one
      _ = maxDiffNorm Γ := by ring
  linarith

private theorem abs_inner_toEuclideanCLM_sub_advForm_le
    (Γ : Matrix (BitString N) (BitString N) ℝ)
    (u v : EuclideanSpace ℝ (BitString N)) (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (U : ℕ → State N W →ₗᵢ[ℂ] State N W) {ψ₀ : State N W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ) :
    |inner ℝ u (Matrix.toEuclideanCLM (𝕜 := ℝ) Γ v) - advForm Γ u v (fun x => run U ψ₀ x T)| ≤
      2 * T * maxDiffNorm Γ := by
  have h0 : inner ℝ u (Matrix.toEuclideanCLM (𝕜 := ℝ) Γ v) =
      advForm Γ u v (fun x => run U ψ₀ x 0) := by
    have hinner : inner ℂ (U 0 ψ₀) (U 0 ψ₀) = (1 : ℂ) := by
      rw [LinearIsometry.inner_map_map, inner_self_eq_norm_sq_to_K, hψ₀]
      simp
    rw [Matrix.inner_toEuclideanCLM]
    simp only [advForm, run, hinner, dotProduct, Matrix.mulVec, mul_sum, RCLike.one_re]
    refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => by ring
  have htele :
      advForm Γ u v (fun x => run U ψ₀ x 0) - advForm Γ u v (fun x => run U ψ₀ x T) =
      ∑ t ∈ range T,
        (advForm Γ u v (fun x => run U ψ₀ x t) - advForm Γ u v (fun x => run U ψ₀ x (t + 1))) :=
    (sum_range_sub' (fun t => advForm Γ u v (fun x => run U ψ₀ x t)) T).symm
  rw [h0, htele]
  calc |∑ t ∈ range T,
        (advForm Γ u v (fun x => run U ψ₀ x t) -
          advForm Γ u v (fun x => run U ψ₀ x (t + 1)))|
      ≤ ∑ t ∈ range T, |advForm Γ u v (fun x => run U ψ₀ x t) -
          advForm Γ u v (fun x => run U ψ₀ x (t + 1))| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t ∈ range T, 2 * maxDiffNorm Γ :=
          sum_le_sum fun t _ => advForm_step_sub_le Γ u v hu hv U hψ₀ t
    _ = 2 * T * maxDiffNorm Γ := by simp; ring

private theorem abs_advForm_final_le_of_proj {α : Type*} {P : BitString N → Prop}
    {f : BitString N → α} {Γ : Matrix (BitString N) (BitString N) ℝ}
    (hΓ : IsAdversaryMatrix P f Γ)
    (u v : EuclideanSpace ℝ (BitString N)) (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (U : ℕ → State N W →ₗᵢ[ℂ] State N W) {ψ₀ : State N W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    (S_out : α → Finset (Fin N × Bool × W)) (hdisj : Pairwise (Disjoint on S_out))
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : 2 * ε ≤ 1)
    (herr : ∀ x, P x → 1 - ε ≤ measureProb (run U ψ₀ x T) (S_out (f x))) :
    |advForm Γ u v (fun x => run U ψ₀ x T)| ≤
      (2 * √(ε * (1 - ε)) + ε) * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ ∧
      (∀ _h : (∀ x y, P x → P y → f x ≠ f y →
          ∀ k, k ∉ S_out (f x) → k ∈ S_out (f y)),
        |advForm Γ u v (fun x => run U ψ₀ x T)| ≤
          2 * √(ε * (1 - ε)) * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖) := by
  classical
  let αs : BitString N → State N W := fun x =>
    if P x then projOutcomes (· ∈ S_out (f x)) (run U ψ₀ x T) else 0
  let βs : BitString N → State N W := fun x =>
    if P x then projOutcomes (fun k => ¬(k ∈ S_out (f x))) (run U ψ₀ x T) else 0
  have hsplit {x y : BitString N} (hxy : Γ x y ≠ 0) :
      RCLike.re (inner ℂ (run U ψ₀ x T) (run U ψ₀ y T)) =
        RCLike.re (inner ℂ (αs x) (βs y)) + RCLike.re (inner ℂ (βs x) (αs y)) +
          RCLike.re (inner ℂ (βs x) (βs y)) := by
    obtain ⟨hx, hy, hf⟩ := hΓ x y hxy
    have hrx : run U ψ₀ x T = αs x + βs x := by
      simp only [αs, βs, hx, ↓reduceIte]
      exact (projOutcomes_add_projOutcomes_not _ _).symm
    have hry : run U ψ₀ y T = αs y + βs y := by
      simp only [αs, βs, hy, ↓reduceIte]
      exact (projOutcomes_add_projOutcomes_not _ _).symm
    have haa : inner ℂ (αs x) (αs y) = 0 := by
      simp only [αs, hx, hy, ↓reduceIte]
      exact inner_projOutcomes_eq_zero _ _
        (fun _ ⟨h1, h2⟩ => Finset.disjoint_left.1 (hdisj hf) h1 h2) _ _
    rw [hrx, hry, inner_add_left, inner_add_right, inner_add_right, haa, zero_add]
    simp only [map_add, add_assoc]
  have hpnorm (φ ψ : BitString N → State N W) :
      |∑ x, ∑ y, Γ x y * u.ofLp x * v.ofLp y * RCLike.re (inner ℂ (φ x) (ψ y))| ≤
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ *
        √(∑ x, (u.ofLp x * ‖φ x‖) ^ 2) * √(∑ y, (v.ofLp y * ‖ψ y‖) ^ 2) :=
    abs_sum_mul_re_inner_le Γ u v φ ψ
  set Au := √(∑ x, (u.ofLp x * ‖αs x‖) ^ 2)
  set Bu := √(∑ x, (u.ofLp x * ‖βs x‖) ^ 2)
  set Av := √(∑ y, (v.ofLp y * ‖αs y‖) ^ 2)
  set Bv := √(∑ y, (v.ofLp y * ‖βs y‖) ^ 2)
  have hnorm_sq (x : BitString N) : ‖αs x‖ ^ 2 + ‖βs x‖ ^ 2 ≤ 1 ∧ ‖βs x‖ ^ 2 ≤ ε := by
    by_cases hx : P x
    · have hmeas : ‖run U ψ₀ x T‖ = 1 := by rw [norm_run, hψ₀]
      have hα : ‖αs x‖ ^ 2 = measureProb (run U ψ₀ x T) (S_out (f x)) := by
        simp only [αs, hx, ↓reduceIte, norm_projOutcomes_sq_mem]
      have hβ : ‖βs x‖ ^ 2 = 1 - measureProb (run U ψ₀ x T) (S_out (f x)) := by
        have hcomp : univ.filter (fun k => ¬(k ∈ S_out (f x))) = (S_out (f x))ᶜ := by
          ext k; simp only [mem_filter, mem_univ, true_and, mem_compl]
        simp only [βs, hx, ↓reduceIte, norm_projOutcomes_sq, hcomp, measureProb_compl, hmeas,
          one_pow]
      have hle := herr x hx
      refine ⟨by linarith, by linarith⟩
    · simp only [αs, βs, hx, ↓reduceIte, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, add_zero, zero_le_one, hε0, and_self]
  have hvec (w : EuclideanSpace ℝ (BitString N)) (hw : ‖w‖ ≤ 1) :
      (√(∑ x, (w.ofLp x * ‖αs x‖) ^ 2)) ^ 2 + (√(∑ x, (w.ofLp x * ‖βs x‖) ^ 2)) ^ 2 ≤ 1 ∧
      (√(∑ x, (w.ofLp x * ‖βs x‖) ^ 2)) ^ 2 ≤ ε := by
    rw [Real.sq_sqrt (sum_nonneg fun _ _ => sq_nonneg _),
      Real.sq_sqrt (sum_nonneg fun _ _ => sq_nonneg _)]
    have hw1 : ∑ x, w.ofLp x ^ 2 ≤ 1 := by
      rw [← EuclideanSpace.real_norm_sq_eq]
      exact pow_le_one₀ (norm_nonneg _) hw
    refine ⟨?_, ?_⟩
    · calc ∑ x, (w.ofLp x * ‖αs x‖) ^ 2 + ∑ x, (w.ofLp x * ‖βs x‖) ^ 2
          = ∑ x, w.ofLp x ^ 2 * (‖αs x‖ ^ 2 + ‖βs x‖ ^ 2) := by
              rw [← sum_add_distrib]
              refine sum_congr rfl fun x _ => by ring
        _ ≤ ∑ x, w.ofLp x ^ 2 * 1 :=
              sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hnorm_sq x).1 (sq_nonneg _)
        _ = ∑ x, w.ofLp x ^ 2 := by simp
        _ ≤ 1 := hw1
    · calc ∑ x, (w.ofLp x * ‖βs x‖) ^ 2
          = ∑ x, w.ofLp x ^ 2 * ‖βs x‖ ^ 2 := sum_congr rfl fun x _ => by ring
        _ ≤ ∑ x, w.ofLp x ^ 2 * ε :=
              sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hnorm_sq x).2 (sq_nonneg _)
        _ = (∑ x, w.ofLp x ^ 2) * ε := (sum_mul _ _ _).symm
        _ ≤ 1 * ε := mul_le_mul_of_nonneg_right hw1 hε0
        _ = ε := one_mul ε
  have hAB : Au * Bv + Bu * Av ≤ 2 * √(ε * (1 - ε)) := by
    have hA_sq : Au ^ 2 + Bu ^ 2 ≤ 1 := (hvec u hu).1
    have hB_sq : Av ^ 2 + Bv ^ 2 ≤ 1 := (hvec v hv).1
    have hBu_le : Bu ^ 2 ≤ ε := (hvec u hu).2
    have hBv_le : Bv ^ 2 ≤ ε := (hvec v hv).2
    have hbd := mul_add_mul_le_two_mul_sqrt (sq_nonneg Bu) (sq_nonneg Bv) hBu_le hBv_le hε
      hA_sq hB_sq
    rwa [Real.sqrt_sq (Real.sqrt_nonneg _), Real.sqrt_sq (Real.sqrt_nonneg _)] at hbd
  have hBB : Bu * Bv ≤ ε := by
    calc Bu * Bv = √(Bu ^ 2) * √(Bv ^ 2) := by
          rw [Real.sqrt_sq (Real.sqrt_nonneg _), Real.sqrt_sq (Real.sqrt_nonneg _)]
      _ ≤ √ε * √ε := mul_le_mul (Real.sqrt_le_sqrt (hvec u hu).2)
            (Real.sqrt_le_sqrt (hvec v hv).2) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = ε := Real.mul_self_sqrt hε0
  have hΓnorm : 0 ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ := norm_nonneg _
  have hterm1 : |∑ x, ∑ y, Γ x y * u.ofLp x * v.ofLp y * RCLike.re (inner ℂ (αs x) (βs y))| ≤
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ * (Au * Bv) := by
    simpa [Au, Bv, mul_assoc] using hpnorm αs βs
  have hterm2 : |∑ x, ∑ y, Γ x y * u.ofLp x * v.ofLp y * RCLike.re (inner ℂ (βs x) (αs y))| ≤
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ * (Bu * Av) := by
    simpa [Bu, Av, mul_assoc] using hpnorm βs αs
  have hterm3 : |∑ x, ∑ y, Γ x y * u.ofLp x * v.ofLp y * RCLike.re (inner ℂ (βs x) (βs y))| ≤
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ * (Bu * Bv) := by
    simpa [Bu, Bv, mul_assoc] using hpnorm βs βs
  have hsum_all :
      advForm Γ u v (fun x => run U ψ₀ x T) =
        (∑ x, ∑ y, Γ x y * u.ofLp x * v.ofLp y * RCLike.re (inner ℂ (αs x) (βs y))) +
        (∑ x, ∑ y, Γ x y * u.ofLp x * v.ofLp y * RCLike.re (inner ℂ (βs x) (αs y))) +
        (∑ x, ∑ y, Γ x y * u.ofLp x * v.ofLp y * RCLike.re (inner ℂ (βs x) (βs y))) := by
    simp only [advForm, ← sum_add_distrib]
    refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
    by_cases hxy0 : Γ x y = 0
    · simp [hxy0]
    · rw [hsplit hxy0]; ring
  refine ⟨?_, fun hβ => ?_⟩
  · calc |advForm Γ u v (fun x => run U ψ₀ x T)|
        ≤ |(∑ x, ∑ y, Γ x y * u.ofLp x * v.ofLp y * RCLike.re (inner ℂ (αs x) (βs y))) +
             (∑ x, ∑ y, Γ x y * u.ofLp x * v.ofLp y * RCLike.re (inner ℂ (βs x) (αs y)))| +
           |∑ x, ∑ y, Γ x y * u.ofLp x * v.ofLp y * RCLike.re (inner ℂ (βs x) (βs y))| := by
            rw [hsum_all]
            exact abs_add_le _ _
      _ ≤ (|∑ x, ∑ y, Γ x y * u.ofLp x * v.ofLp y * RCLike.re (inner ℂ (αs x) (βs y))| +
             |∑ x, ∑ y, Γ x y * u.ofLp x * v.ofLp y * RCLike.re (inner ℂ (βs x) (αs y))|) +
           |∑ x, ∑ y, Γ x y * u.ofLp x * v.ofLp y * RCLike.re (inner ℂ (βs x) (βs y))| :=
            add_le_add (abs_add_le _ _) le_rfl
      _ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ * (Au * Bv) +
            ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ * (Bu * Av) +
            ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ * (Bu * Bv) :=
            add_le_add (add_le_add hterm1 hterm2) hterm3
      _ = (Au * Bv + Bu * Av + Bu * Bv) * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ := by ring
      _ ≤ (2 * √(ε * (1 - ε)) + ε) * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ :=
            mul_le_mul_of_nonneg_right (add_le_add hAB hBB) hΓnorm
  · have hβzero :
        ∑ x, ∑ y, Γ x y * u.ofLp x * v.ofLp y * RCLike.re (inner ℂ (βs x) (βs y)) = 0 := by
      refine sum_eq_zero fun x _ => sum_eq_zero fun y _ => ?_
      by_cases hxy0 : Γ x y = 0
      · simp [hxy0]
      · obtain ⟨hx, hy, hf⟩ := hΓ x y hxy0
        have hbb : inner ℂ (βs x) (βs y) = 0 := by
          simp only [βs, hx, hy, ↓reduceIte]
          exact inner_projOutcomes_eq_zero _ _ (fun k ⟨h1, h2⟩ => h2 (hβ x y hx hy hf k h1)) _ _
        simp [hbb]
    rw [hsum_all, hβzero, add_zero]
    calc |(∑ x, ∑ y, Γ x y * u.ofLp x * v.ofLp y * RCLike.re (inner ℂ (αs x) (βs y))) +
          (∑ x, ∑ y, Γ x y * u.ofLp x * v.ofLp y * RCLike.re (inner ℂ (βs x) (αs y)))|
        ≤ |∑ x, ∑ y, Γ x y * u.ofLp x * v.ofLp y * RCLike.re (inner ℂ (αs x) (βs y))| +
          |∑ x, ∑ y, Γ x y * u.ofLp x * v.ofLp y * RCLike.re (inner ℂ (βs x) (αs y))| :=
          abs_add_le _ _
      _ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ * (Au * Bv) +
            ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ * (Bu * Av) := add_le_add hterm1 hterm2
      _ = (Au * Bv + Bu * Av) * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ := by ring
      _ ≤ (2 * √(ε * (1 - ε))) * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ :=
            mul_le_mul_of_nonneg_right hAB hΓnorm

/-- **Negative-weight adversary bound for Boolean outputs** ([HoyerLeeSpalek2007], Theorem 2):
for any real matrix `Γ` supported on `{(x, y) | P x ∧ P y ∧ f x ≠ f y}` and any `T`-query
algorithm accepting `x ∈ P` with `f x = true` with probability at least `1 - ε` and accepting
`x ∈ P` with `f x = false` with probability at most `ε ≤ 1/2`,
`(1 - 2√(ε(1-ε))) ‖Γ‖ ≤ 2 T · maxDiffNorm Γ`. -/
theorem one_sub_mul_opNorm_le_general_boolean {P : BitString N → Prop}
    {f : BitString N → Bool} {Γ : Matrix (BitString N) (BitString N) ℝ}
    (hΓ : IsAdversaryMatrix P f Γ)
    (U : ℕ → State N W →ₗᵢ[ℂ] State N W) {ψ₀ : State N W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    (S_acc : Finset (Fin N × Bool × W)) {ε : ℝ} (hε0 : 0 ≤ ε) (hε : 2 * ε ≤ 1)
    (h₁ : ∀ x, P x → f x = true → 1 - ε ≤ measureProb (run U ψ₀ x T) S_acc)
    (h₀ : ∀ x, P x → f x = false → measureProb (run U ψ₀ x T) S_acc ≤ ε) :
    (1 - 2 * √(ε * (1 - ε))) * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ ≤
      2 * T * maxDiffNorm Γ := by
  classical
  let S_out : Bool → Finset (Fin N × Bool × W) := fun b => if b then S_acc else S_accᶜ
  have hdisj : Pairwise (Disjoint on S_out) := by
    intro b₁ b₂ hne
    cases b₁ <;> cases b₂
    · exact absurd rfl hne
    · change Disjoint S_accᶜ S_acc
      exact disjoint_compl_left
    · change Disjoint S_acc S_accᶜ
      exact disjoint_compl_right
    · exact absurd rfl hne
  have herr : ∀ x, P x → 1 - ε ≤ measureProb (run U ψ₀ x T) (S_out (f x)) := by
    intro x hx
    cases hfx : f x
    · simp only [S_out, Bool.false_eq_true, ↓reduceIte, measureProb_compl, norm_run, hψ₀, one_pow]
      linarith [h₀ x hx hfx]
    · simpa [S_out, hfx] using h₁ x hx hfx
  have hcomp : ∀ x y, P x → P y → f x ≠ f y → ∀ k, k ∉ S_out (f x) → k ∈ S_out (f y) := by
    intro x y _ _ hne k hk
    cases hfx : f x <;> cases hfy : f y
    · exact absurd (hfx.trans hfy.symm) hne
    · simp only [S_out, hfx, Bool.false_eq_true, ↓reduceIte, mem_compl] at hk ⊢
      exact not_not.1 hk
    · simp only [S_out, hfx, Bool.false_eq_true, ↓reduceIte, mem_compl] at hk ⊢
      exact hk
    · exact absurd (hfx.trans hfy.symm) hne
  have hbound : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ ≤
      2 * √(ε * (1 - ε)) * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ + 2 * T * maxDiffNorm Γ := by
    have hnn : 0 ≤ 2 * √(ε * (1 - ε)) * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ +
        2 * T * maxDiffNorm Γ :=
      add_nonneg (mul_nonneg (mul_nonneg zero_le_two (Real.sqrt_nonneg _)) (norm_nonneg _))
        (mul_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg _)) (maxDiffNorm_nonneg _))
    refine Matrix.opNorm_toEuclideanCLM_le_of_inner Γ hnn fun u v hu hv => ?_
    have ht := abs_inner_toEuclideanCLM_sub_advForm_le Γ u v hu hv U hψ₀ T
    have hf := (abs_advForm_final_le_of_proj hΓ u v hu hv U hψ₀ T S_out hdisj hε0 hε herr).2 hcomp
    linarith [le_abs_self (inner ℝ u (Matrix.toEuclideanCLM (𝕜 := ℝ) Γ v)),
      (abs_le.1 ht).2, (abs_le.1 hf).2]
  linarith

private theorem c_mul_generalAdversary_le {α : Type*} {P : BitString N → Prop}
    {f : BitString N → α} {c : ℝ} {T : ℕ}
    (hc_mat : ∀ Γ : Matrix (BitString N) (BitString N) ℝ, Γ.IsSymm → IsAdversaryMatrix P f Γ →
      c * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ ≤ 2 * T * maxDiffNorm Γ) :
    c * generalAdversary P f ≤ 2 * T := by
  rcases le_or_gt c 0 with hc0 | hcpos
  · exact (mul_nonpos_of_nonpos_of_nonneg hc0 (generalAdversary_nonneg P f)).trans (by positivity)
  · rw [mul_comm, ← le_div_iff₀ hcpos]
    refine csSup_le ⟨0, 0, Matrix.isSymm_zero, fun _ _ h => (h rfl).elim, by simp⟩ ?_
    rintro r ⟨Γ, hsym, hΓ, rfl⟩
    rw [le_div_iff₀ hcpos]
    by_cases hm0 : maxDiffNorm Γ = 0
    · simp only [hm0, div_zero, zero_mul]; positivity
    · have hm : 0 < maxDiffNorm Γ := lt_of_le_of_ne (maxDiffNorm_nonneg Γ) (Ne.symm hm0)
      have hbd := hc_mat Γ hsym hΓ
      rw [div_mul_eq_mul_div, div_le_iff₀ hm]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hbd

/-- **Negative-weight adversary lower bound `ADV±(f)` for Boolean functions**
([HoyerLeeSpalek2007], Theorem 2):
`(1 - 2√(ε(1-ε))) ADV±(f) ≤ 2 T`. -/
theorem one_sub_mul_generalAdversary_le_boolean {P : BitString N → Prop}
    {f : BitString N → Bool} (U : ℕ → State N W →ₗᵢ[ℂ] State N W)
    {ψ₀ : State N W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    (S_acc : Finset (Fin N × Bool × W)) {ε : ℝ} (hε0 : 0 ≤ ε) (hε : 2 * ε ≤ 1)
    (h₁ : ∀ x, P x → f x = true → 1 - ε ≤ measureProb (run U ψ₀ x T) S_acc)
    (h₀ : ∀ x, P x → f x = false → measureProb (run U ψ₀ x T) S_acc ≤ ε) :
    (1 - 2 * √(ε * (1 - ε))) * generalAdversary P f ≤ 2 * T :=
  c_mul_generalAdversary_le fun _ _ hΓ =>
    one_sub_mul_opNorm_le_general_boolean hΓ U hψ₀ T S_acc hε0 hε h₁ h₀

/-- **Negative-weight adversary bound for arbitrary finite output alphabets**: if a `T`-query
algorithm outputs `f x` with probability at least `1 - ε` (`ε ≤ 1/2`) via pairwise disjoint
outcome regions `S_out a`, then `(1 - 2√(ε(1-ε)) - ε) ‖Γ‖ ≤ 2 T · maxDiffNorm Γ`. -/
theorem one_sub_mul_opNorm_le_general {α : Type*} {P : BitString N → Prop}
    {f : BitString N → α} {Γ : Matrix (BitString N) (BitString N) ℝ}
    (hΓ : IsAdversaryMatrix P f Γ)
    (U : ℕ → State N W →ₗᵢ[ℂ] State N W) {ψ₀ : State N W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    (S_out : α → Finset (Fin N × Bool × W)) (hdisj : Pairwise (Disjoint on S_out))
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : 2 * ε ≤ 1)
    (herr : ∀ x, P x → 1 - ε ≤ measureProb (run U ψ₀ x T) (S_out (f x))) :
    (1 - 2 * √(ε * (1 - ε)) - ε) * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ ≤
      2 * T * maxDiffNorm Γ := by
  have hbound : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ ≤
      (2 * √(ε * (1 - ε)) + ε) * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ + 2 * T * maxDiffNorm Γ := by
    have hnn : 0 ≤ (2 * √(ε * (1 - ε)) + ε) * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ +
        2 * T * maxDiffNorm Γ :=
      add_nonneg (mul_nonneg (add_nonneg (mul_nonneg zero_le_two (Real.sqrt_nonneg _)) hε0)
        (norm_nonneg _))
        (mul_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg _)) (maxDiffNorm_nonneg _))
    refine Matrix.opNorm_toEuclideanCLM_le_of_inner Γ hnn fun u v hu hv => ?_
    have ht := abs_inner_toEuclideanCLM_sub_advForm_le Γ u v hu hv U hψ₀ T
    have hf := (abs_advForm_final_le_of_proj hΓ u v hu hv U hψ₀ T S_out hdisj hε0 hε herr).1
    linarith [le_abs_self (inner ℝ u (Matrix.toEuclideanCLM (𝕜 := ℝ) Γ v)),
      (abs_le.1 ht).2, (abs_le.1 hf).2]
  linarith

/-- Weakened form matching [HoyerLeeSpalek2007], Theorem 2:
`(1 - 2√(ε(1-ε)) - 2ε) ‖Γ‖ ≤ 2 T · maxDiffNorm Γ`. -/
theorem one_sub_mul_opNorm_le_general_hls {α : Type*} {P : BitString N → Prop}
    {f : BitString N → α} {Γ : Matrix (BitString N) (BitString N) ℝ}
    (hΓ : IsAdversaryMatrix P f Γ)
    (U : ℕ → State N W →ₗᵢ[ℂ] State N W) {ψ₀ : State N W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    (S_out : α → Finset (Fin N × Bool × W)) (hdisj : Pairwise (Disjoint on S_out))
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : 2 * ε ≤ 1)
    (herr : ∀ x, P x → 1 - ε ≤ measureProb (run U ψ₀ x T) (S_out (f x))) :
    (1 - 2 * √(ε * (1 - ε)) - 2 * ε) * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ ≤
      2 * T * maxDiffNorm Γ := by
  have hb := one_sub_mul_opNorm_le_general hΓ U hψ₀ T S_out hdisj hε0 hε herr
  nlinarith [norm_nonneg (Matrix.toEuclideanCLM (𝕜 := ℝ) Γ)]

/-- **Negative-weight adversary bound `ADV±(f)` for finite outputs**:
`(1 - 2√(ε(1-ε)) - ε) ADV±(f) ≤ 2 T`. -/
theorem one_sub_mul_generalAdversary_le {α : Type*} {P : BitString N → Prop}
    {f : BitString N → α} (U : ℕ → State N W →ₗᵢ[ℂ] State N W)
    {ψ₀ : State N W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    (S_out : α → Finset (Fin N × Bool × W)) (hdisj : Pairwise (Disjoint on S_out))
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : 2 * ε ≤ 1)
    (herr : ∀ x, P x → 1 - ε ≤ measureProb (run U ψ₀ x T) (S_out (f x))) :
    (1 - 2 * √(ε * (1 - ε)) - ε) * generalAdversary P f ≤ 2 * T :=
  c_mul_generalAdversary_le fun _ _ hΓ =>
    one_sub_mul_opNorm_le_general hΓ U hψ₀ T S_out hdisj hε0 hε herr

/-- Weakened form matching [HoyerLeeSpalek2007], Theorem 2:
`(1 - 2√(ε(1-ε)) - 2ε) ADV±(f) ≤ 2 T`. -/
theorem one_sub_mul_generalAdversary_le_hls {α : Type*} {P : BitString N → Prop}
    {f : BitString N → α} (U : ℕ → State N W →ₗᵢ[ℂ] State N W)
    {ψ₀ : State N W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    (S_out : α → Finset (Fin N × Bool × W)) (hdisj : Pairwise (Disjoint on S_out))
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : 2 * ε ≤ 1)
    (herr : ∀ x, P x → 1 - ε ≤ measureProb (run U ψ₀ x T) (S_out (f x))) :
    (1 - 2 * √(ε * (1 - ε)) - 2 * ε) * generalAdversary P f ≤ 2 * T :=
  c_mul_generalAdversary_le fun _ _ hΓ =>
    one_sub_mul_opNorm_le_general_hls hΓ U hψ₀ T S_out hdisj hε0 hε herr

/-- **Nonnegative spectral adversary matrix bound** ([BarnumSaksSzegedy2003], as reviewed in
[HoyerLeeSpalek2007], Section 1.1, Theorem 1): when `0 ≤ Γ` and `Γ` is supported on
`{(x, y) | P x ∧ P y ∧ f x ≠ f y}`, a final-state overlap bound `δ` yields
`(1 - δ) ‖Γ‖ ≤ 2 T · maxDiffNorm Γ` for any output type `α`. -/
theorem one_sub_mul_opNorm_le_spectral {α : Type*} {P : BitString N → Prop}
    {f : BitString N → α} {Γ : Matrix (BitString N) (BitString N) ℝ}
    (hnonneg : ∀ x y, 0 ≤ Γ x y) (hΓ : IsAdversaryMatrix P f Γ)
    (U : ℕ → State N W →ₗᵢ[ℂ] State N W) {ψ₀ : State N W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    {δ : ℝ} (hδ : ∀ x y, P x → P y → f x ≠ f y →
      ‖inner ℂ (run U ψ₀ x T) (run U ψ₀ y T)‖ ≤ δ) :
    (1 - δ) * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ ≤ 2 * T * maxDiffNorm Γ := by
  by_cases hzero : Γ = 0
  · simp only [hzero, map_zero, norm_zero, mul_zero]
    exact mul_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg T)) (maxDiffNorm_nonneg 0)
  have hne : ∃ x y, Γ x y ≠ 0 := by
    by_contra h
    push Not at h
    exact hzero (Matrix.ext fun x y => h x y)
  obtain ⟨x₀, y₀, hxy0⟩ := hne
  have hδ0 : 0 ≤ δ := by
    obtain ⟨hx₀, hy₀, hf₀⟩ := hΓ x₀ y₀ hxy0
    exact (norm_nonneg _).trans (hδ x₀ y₀ hx₀ hy₀ hf₀)
  have hbound : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ ≤
      δ * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ + 2 * T * maxDiffNorm Γ := by
    have hnn : 0 ≤ δ * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ + 2 * T * maxDiffNorm Γ :=
      add_nonneg (mul_nonneg hδ0 (norm_nonneg _))
        (mul_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg _)) (maxDiffNorm_nonneg _))
    refine Matrix.opNorm_toEuclideanCLM_le_of_inner Γ hnn fun u v hu hv => ?_
    have huPos := Matrix.norm_absVec_le hu
    have hvPos := Matrix.norm_absVec_le hv
    have h0_le := Matrix.inner_toEuclideanCLM_le_absVec hnonneg u v
    have ht := abs_inner_toEuclideanCLM_sub_advForm_le Γ (Matrix.absVec u) (Matrix.absVec v)
      huPos hvPos U hψ₀ T
    have hf : advForm Γ (Matrix.absVec u) (Matrix.absVec v) (fun x => run U ψ₀ x T) ≤
        δ * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ := by
      calc advForm Γ (Matrix.absVec u) (Matrix.absVec v) (fun x => run U ψ₀ x T)
          ≤ ∑ x, ∑ y, Γ x y * |u.ofLp x| * |v.ofLp y| * δ := by
              refine sum_le_sum fun x _ => sum_le_sum fun y _ => ?_
              by_cases hxy : Γ x y = 0
              · simp [hxy]
              · obtain ⟨hx, hy, hf⟩ := hΓ x y hxy
                have hre : RCLike.re (inner ℂ (run U ψ₀ x T) (run U ψ₀ y T)) ≤ δ :=
                  (RCLike.re_le_norm _).trans (hδ x y hx hy hf)
                exact mul_le_mul_of_nonneg_left hre (mul_nonneg (mul_nonneg (hnonneg x y)
                  (abs_nonneg _)) (abs_nonneg _))
        _ = δ * inner ℝ (Matrix.absVec u) (Matrix.toEuclideanCLM (𝕜 := ℝ) Γ (Matrix.absVec v)) := by
              rw [Matrix.inner_toEuclideanCLM]
              simp only [dotProduct, Matrix.mulVec, mul_sum, Matrix.absVec_apply]
              refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => by ring
        _ ≤ δ * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ := by
              refine mul_le_mul_of_nonneg_left ?_ hδ0
              calc inner ℝ (Matrix.absVec u)
                    (Matrix.toEuclideanCLM (𝕜 := ℝ) Γ (Matrix.absVec v))
                  ≤ ‖Matrix.absVec u‖ *
                      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ (Matrix.absVec v)‖ :=
                    real_inner_le_norm _ _
                _ ≤ 1 * (‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ * ‖Matrix.absVec v‖) :=
                    mul_le_mul huPos (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _) zero_le_one
                _ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ * 1 := by
                    rw [one_mul]; exact mul_le_mul_of_nonneg_left hvPos (norm_nonneg _)
                _ = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ := mul_one _
    linarith [(abs_le.1 ht).2]
  linarith

/-- **Nonnegative spectral adversary lower bound `ADV(f)`** ([BarnumSaksSzegedy2003],
Section 1.1 of [HoyerLeeSpalek2007]):
`(1 - δ) ADV(f) ≤ 2 T` from any final-state overlap bound `δ`. -/
theorem one_sub_mul_spectralAdversary_le_of_inner {α : Type*} {P : BitString N → Prop}
    {f : BitString N → α} (U : ℕ → State N W →ₗᵢ[ℂ] State N W)
    {ψ₀ : State N W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ) {δ : ℝ}
    (hδ : ∀ x y, P x → P y → f x ≠ f y → ‖inner ℂ (run U ψ₀ x T) (run U ψ₀ y T)‖ ≤ δ) :
    (1 - δ) * spectralAdversary P f ≤ 2 * T := by
  rcases le_or_gt (1 - δ) 0 with hc0 | hcpos
  · exact (mul_nonpos_of_nonpos_of_nonneg hc0 (spectralAdversary_nonneg P f)).trans (by positivity)
  · rw [mul_comm, ← le_div_iff₀ hcpos]
    refine csSup_le ⟨0, 0, Matrix.isSymm_zero, fun _ _ => le_rfl,
      fun _ _ h => (h rfl).elim, by simp⟩ ?_
    rintro r ⟨Γ, -, hnonneg, hΓ, rfl⟩
    rw [le_div_iff₀ hcpos]
    by_cases hm0 : maxDiffNorm Γ = 0
    · simp only [hm0, div_zero, zero_mul]; positivity
    · have hm : 0 < maxDiffNorm Γ := lt_of_le_of_ne (maxDiffNorm_nonneg Γ) (Ne.symm hm0)
      have hbd := one_sub_mul_opNorm_le_spectral hnonneg hΓ U hψ₀ T hδ
      rw [div_mul_eq_mul_div, div_le_iff₀ hm]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hbd

/-- **Nonnegative spectral adversary lower bound `ADV(f)`** for finite-output algorithms with
error probability at most `ε ≤ 1/2`: `(1 - 2√(ε(1-ε))) ADV(f) ≤ 2 T`. -/
theorem one_sub_mul_spectralAdversary_le {α : Type*} {P : BitString N → Prop}
    {f : BitString N → α} (U : ℕ → State N W →ₗᵢ[ℂ] State N W)
    {ψ₀ : State N W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    (S_out : α → Finset (Fin N × Bool × W)) (hdisj : Pairwise (Disjoint on S_out))
    {ε : ℝ} (hε : 2 * ε ≤ 1)
    (herr : ∀ x, P x → 1 - ε ≤ measureProb (run U ψ₀ x T) (S_out (f x))) :
    (1 - 2 * √(ε * (1 - ε))) * spectralAdversary P f ≤ 2 * T := by
  classical
  refine one_sub_mul_spectralAdversary_le_of_inner U hψ₀ T fun x y hx hy hf => ?_
  have hdisjxy := hdisj hf
  have h1 := herr x hx
  have h2 : measureProb (run U ψ₀ y T) (S_out (f x)) ≤ ε := by
    have hsub := measureProb_mono (run U ψ₀ y T) hdisjxy.le_compl_right
    have hc : measureProb (run U ψ₀ y T) (S_out (f y))ᶜ ≤ ε := by
      rw [measureProb_compl, norm_run, hψ₀, one_pow]
      linarith [herr y hy]
    exact hsub.trans hc
  exact norm_inner_le_two_mul_sqrt_of_measureProb (by rw [norm_run, hψ₀])
    (by rw [norm_run, hψ₀]) h1 h2 hε

end ProgressCore

section HierarchyAndBarriers

/-- **Spectral sensitivity is at most the nonnegative spectral adversary**
([AaronsonBenDavidKothariRaoTal2021], via the sensitivity-graph adjacency matrix):
`λ(f) ≤ ADV(f)`. -/
theorem spectralSensitivity_le_spectralAdversary (f : BooleanFunction N) :
    BitString.spectralSensitivity f ≤ spectralAdversary (fun _ => True) f := by
  let Γ := (BitString.sensitivityGraph f).adjMatrix ℝ
  have hsym : Γ.IsSymm := SimpleGraph.isSymm_adjMatrix _
  have hnonneg : ∀ x y, 0 ≤ Γ x y := fun x y => by
    simp only [Γ, SimpleGraph.adjMatrix_apply]
    split_ifs <;> norm_num
  have hΓ : IsAdversaryMatrix (fun _ => True) f Γ := by
    intro x y hne
    have hadj : (BitString.sensitivityGraph f).Adj x y := by
      simpa [Γ, SimpleGraph.adjMatrix_apply] using hne
    obtain ⟨i, hi, rfl⟩ := BitString.sensitivityGraph_adj.1 hadj
    exact ⟨trivial, trivial, Ne.symm hi⟩
  have hmax : maxDiffNorm Γ ≤ 1 := by
    refine (maxDiffNorm_le_iff zero_le_one).2 fun i => ?_
    refine (Matrix.opNorm_toEuclideanCLM_le_sqrt _ zero_le_one zero_le_one
      (fun x => ?_) (fun y => ?_)).trans (by simp)
    · have hrow : ∑ y, |(Γ.hadamard (diffMatrix i)) x y| =
          if (BitString.sensitivityGraph f).Adj x (Function.update x i (!x i)) then 1 else 0 := by
        rw [Finset.sum_eq_single (Function.update x i (!x i))]
        · by_cases hadj : (BitString.sensitivityGraph f).Adj x (Function.update x i (!x i)) <;>
            simp [Γ, hadj]
        · intro y _ hyne
          by_cases hadj : (BitString.sensitivityGraph f).Adj x y
          · obtain ⟨j, hj, rfl⟩ := BitString.sensitivityGraph_adj.1 hadj
            have hji : j ≠ i := fun h => hyne (by subst h; rfl)
            simp [Function.update_of_ne hji.symm]
          · simp [Γ, hadj]
        · intro hmem; exact absurd (mem_univ _) hmem
      rw [hrow]
      split_ifs <;> norm_num
    · have hcol : ∑ x, |(Γ.hadamard (diffMatrix i)) x y| =
          if (BitString.sensitivityGraph f).Adj (Function.update y i (!y i)) y then 1 else 0 := by
        rw [Finset.sum_eq_single (Function.update y i (!y i))]
        · by_cases hadj : (BitString.sensitivityGraph f).Adj (Function.update y i (!y i)) y <;>
            simp [Γ, hadj]
        · intro x _ hxne
          by_cases hadj : (BitString.sensitivityGraph f).Adj x y
          · obtain ⟨j, -, rfl⟩ := BitString.sensitivityGraph_adj.1 hadj
            have hji : j ≠ i := by
              intro h; subst h
              exact hxne (by
                simp only [Function.update_self, Bool.not_not, Function.update_idem,
                  Function.update_eq_self])
            simp [Function.update_of_ne hji.symm]
          · simp [Γ, hadj]
        · intro hmem; exact absurd (mem_univ _) hmem
      rw [hcol]
      split_ifs <;> norm_num
  have hspec_le : BitString.spectralSensitivity f ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ := by
    refine BitString.spectralSensitivity_le_of_forall_sum_le (norm_nonneg _)
      fun u w _ _ hu1 hw1 => ?_
    rw [← BitString.inner_toEuclideanCLM_adjMatrix_sensitivityGraph]
    set u' : EuclideanSpace ℝ (BitString N) := WithLp.toLp 2 u
    set w' : EuclideanSpace ℝ (BitString N) := WithLp.toLp 2 w
    have hu' : ‖u'‖ = 1 := by
      have hu_sq : ‖u'‖ ^ 2 = 1 := by
        rw [EuclideanSpace.real_norm_sq_eq]
        exact hu1
      nlinarith [norm_nonneg u']
    have hw' : ‖w'‖ = 1 := by
      have hw_sq : ‖w'‖ ^ 2 = 1 := by
        rw [EuclideanSpace.real_norm_sq_eq]
        exact hw1
      nlinarith [norm_nonneg w']
    calc inner ℝ u' (Matrix.toEuclideanCLM (𝕜 := ℝ) Γ w')
        ≤ ‖u'‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ w'‖ := real_inner_le_norm _ _
      _ ≤ 1 * (‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ * ‖w'‖) := by
          rw [hu']
          exact mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) zero_le_one
      _ = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ := by rw [hw', mul_one, one_mul]
  have hle := le_spectralAdversary hsym hnonneg hΓ
  by_cases hm0 : maxDiffNorm Γ = 0
  · have hΓ0 := eq_zero_of_maxDiffNorm_eq_zero hΓ hm0
    have hlam0 : BitString.spectralSensitivity f ≤ 0 := by
      simpa [hΓ0] using hspec_le
    exact hlam0.trans (spectralAdversary_nonneg _ _)
  · have hm : 0 < maxDiffNorm Γ := lt_of_le_of_ne (maxDiffNorm_nonneg Γ) (Ne.symm hm0)
    calc BitString.spectralSensitivity f ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ / 1 := by
          simpa using hspec_le
      _ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ / maxDiffNorm Γ :=
          div_le_div_of_nonneg_left (norm_nonneg _) hm hmax
      _ ≤ spectralAdversary (fun _ => True) f := hle

/-- Weight matrix `A[x, y] = ∑_{p ∈ S.R, p = (x, y)} S.w p` associated with a weight scheme. -/
private noncomputable def wsRaw (S : WeightScheme N) : Matrix (BitString N) (BitString N) ℝ :=
  Matrix.of fun x y => ∑ p ∈ S.R with p = (x, y), S.w p

/-- Normalized nonnegative symmetric matrix associated with a weight scheme `S`:
`Γ[x, y] = (A[x, y] + A[y, x]) / (z(x) z(y))` with `z(x) = √(wtFst x + wtSnd x)`. -/
private noncomputable def wsMatrix (S : WeightScheme N) : Matrix (BitString N) (BitString N) ℝ :=
  Matrix.of fun x y =>
    (wsRaw S x y + wsRaw S y x) / (√(S.wtFst x + S.wtSnd x) * √(S.wtFst y + S.wtSnd y))

private theorem wsMatrix_isSymm (S : WeightScheme N) : (wsMatrix S).IsSymm := by
  ext x y
  simp only [Matrix.transpose_apply, wsMatrix, Matrix.of_apply]
  ring

private theorem wsMatrix_nonneg (S : WeightScheme N) (x y : BitString N) : 0 ≤ wsMatrix S x y := by
  classical
  refine div_nonneg (add_nonneg ?_ ?_) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) <;>
    exact sum_nonneg fun p hp => S.w_nonneg p (mem_filter.1 hp).1

private theorem wsMatrix_isAdversary {α : Type*} {P : BitString N → Prop} {f : BitString N → α}
    (S : WeightScheme N) (hS : ∀ p ∈ S.R, P p.1 ∧ P p.2 ∧ f p.1 ≠ f p.2) :
    IsAdversaryMatrix P f (wsMatrix S) := by
  classical
  intro x y hne
  have hA_ne : wsRaw S x y ≠ 0 ∨ wsRaw S y x ≠ 0 := by
    by_contra hboth
    push Not at hboth
    simp [wsMatrix, hboth.1, hboth.2] at hne
  rcases hA_ne with h1 | h2
  · obtain ⟨p, hp, _⟩ := exists_ne_zero_of_sum_ne_zero h1
    obtain ⟨hpR, hpx⟩ := mem_filter.1 hp
    have hsub := hS _ hpR
    rw [hpx] at hsub
    exact hsub
  · obtain ⟨p, hp, _⟩ := exists_ne_zero_of_sum_ne_zero h2
    obtain ⟨hpR, hpy⟩ := mem_filter.1 hp
    have hsub := hS _ hpR
    rw [hpy] at hsub
    exact ⟨hsub.2.1, hsub.1, hsub.2.2.symm⟩

private theorem wsMatrix_opNorm_ge_one (S : WeightScheme N) (hW : 0 < S.weightSum) :
    1 ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (wsMatrix S)‖ := by
  classical
  let z : BitString N → ℝ := fun x => √(S.wtFst x + S.wtSnd x)
  have hmul_self (x y : BitString N) :
      wsMatrix S x y * (z x * z y) = wsRaw S x y + wsRaw S y x := by
    by_cases hz : z x * z y = 0
    · have hwt_le (u v : BitString N) (hzu : z u = 0) : wsRaw S u v = 0 ∧ wsRaw S v u = 0 := by
        have hsum0 : S.wtFst u + S.wtSnd u = 0 := by
          have := congrArg (· ^ 2) hzu
          rw [Real.sq_sqrt (add_nonneg (S.wtFst_nonneg u) (S.wtSnd_nonneg u))] at this
          simpa using this
        have h1 : S.wtFst u = 0 := le_antisymm (by linarith [S.wtSnd_nonneg u]) (S.wtFst_nonneg u)
        have h2 : S.wtSnd u = 0 := le_antisymm (by linarith [S.wtFst_nonneg u]) (S.wtSnd_nonneg u)
        refine ⟨sum_eq_zero fun p hp => ?_, sum_eq_zero fun p hp => ?_⟩
        · obtain ⟨hpR, hpuv⟩ := mem_filter.1 hp
          exact (sum_eq_zero_iff_of_nonneg fun q hq => S.w_nonneg q (mem_filter.1 hq).1).1 h1
            p (mem_filter.2 ⟨hpR, congrArg Prod.fst hpuv⟩)
        · obtain ⟨hpR, hpvu⟩ := mem_filter.1 hp
          exact (sum_eq_zero_iff_of_nonneg fun q hq => S.w_nonneg q (mem_filter.1 hq).1).1 h2
            p (mem_filter.2 ⟨hpR, congrArg Prod.snd hpvu⟩)
      rcases mul_eq_zero.1 hz with hzx | hzy
      · obtain ⟨h1, h2⟩ := hwt_le x y hzx
        simp [wsMatrix, z, hz, h1, h2]
      · obtain ⟨h1, h2⟩ := hwt_le y x hzy
        simp [wsMatrix, z, hz, h1, h2]
    · exact div_mul_cancel₀ _ hz
  let w₀ : EuclideanSpace ℝ (BitString N) := WithLp.toLp 2 fun x => z x / √(2 * S.weightSum)
  have hfst : ∑ x, S.wtFst x = S.weightSum := by
    rw [← S.sum_wtFst_eq_weightSum]
    exact (sum_subset (subset_univ _) fun x _ hx => by
      refine sum_eq_zero fun p hp => ?_
      exact absurd (mem_image.2 ⟨p, (mem_filter.1 hp).1, (mem_filter.1 hp).2⟩) hx).symm
  have hw₀_sq : ‖w₀‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    have hsnd : ∑ y, S.wtSnd y = S.weightSum := by
      rw [← S.sum_wtSnd_eq_weightSum]
      exact (sum_subset (subset_univ _) fun y _ hy => by
        refine sum_eq_zero fun p hp => ?_
        exact absurd (mem_image.2 ⟨p, (mem_filter.1 hp).1, (mem_filter.1 hp).2⟩) hy).symm
    calc ∑ x, (z x / √(2 * S.weightSum)) ^ 2
        = (∑ x, (S.wtFst x + S.wtSnd x)) / (2 * S.weightSum) := by
            rw [sum_div]
            refine sum_congr rfl fun x _ => ?_
            rw [div_pow, Real.sq_sqrt (add_nonneg (S.wtFst_nonneg x) (S.wtSnd_nonneg x)),
              Real.sq_sqrt (by linarith)]
      _ = (S.weightSum + S.weightSum) / (2 * S.weightSum) := by
            rw [sum_add_distrib, hfst, hsnd]
      _ = 1 := by field_simp [hW.ne']; ring
  have hw₀ : ‖w₀‖ = 1 := by nlinarith [norm_nonneg w₀]
  have hA_sum : ∑ x, ∑ y, wsRaw S x y = S.weightSum := by
    calc ∑ x, ∑ y, wsRaw S x y
        = ∑ x, S.wtFst x := by
          refine sum_congr rfl fun x _ => ?_
          rw [WeightScheme.wtFst, ← sum_fiberwise_of_maps_to (s := S.R.filter fun p => p.1 = x)
            (g := Prod.snd) (t := univ) (fun _ _ => mem_univ _)]
          refine sum_congr rfl fun y _ => sum_congr ?_ fun _ _ => rfl
          ext p
          simp only [mem_filter, Prod.ext_iff, and_assoc]
      _ = S.weightSum := hfst
  have hA_sym : ∑ x, ∑ y, wsRaw S y x = S.weightSum := by
    rw [sum_comm]; exact hA_sum
  have hray : inner ℝ w₀ (Matrix.toEuclideanCLM (𝕜 := ℝ) (wsMatrix S) w₀) = 1 := by
    rw [Matrix.inner_toEuclideanCLM]
    simp only [dotProduct, Matrix.mulVec, w₀, mul_sum]
    calc ∑ x, ∑ y, (z x / √(2 * S.weightSum)) * (wsMatrix S x y * (z y / √(2 * S.weightSum)))
        = (∑ x, ∑ y, (wsRaw S x y + wsRaw S y x)) / (2 * S.weightSum) := by
            rw [sum_div]
            refine sum_congr rfl fun x _ => by
              rw [sum_div]
              refine sum_congr rfl fun y _ => ?_
              calc (z x / √(2 * S.weightSum)) * (wsMatrix S x y * (z y / √(2 * S.weightSum)))
                  = (wsMatrix S x y * (z x * z y)) / (√(2 * S.weightSum) * √(2 * S.weightSum)) :=
                    by ring
                _ = (wsRaw S x y + wsRaw S y x) / (2 * S.weightSum) := by
                    rw [hmul_self, Real.mul_self_sqrt (by linarith)]
      _ = (S.weightSum + S.weightSum) / (2 * S.weightSum) := by
            simp only [sum_add_distrib, hA_sum, hA_sym]
      _ = 1 := by field_simp [hW.ne']; ring
  calc (1 : ℝ) = inner ℝ w₀ (Matrix.toEuclideanCLM (𝕜 := ℝ) (wsMatrix S) w₀) := hray.symm
    _ ≤ ‖w₀‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (wsMatrix S) w₀‖ := real_inner_le_norm _ _
    _ ≤ ‖w₀‖ * (‖Matrix.toEuclideanCLM (𝕜 := ℝ) (wsMatrix S)‖ * ‖w₀‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (wsMatrix S)‖ := by rw [hw₀, mul_one, one_mul]

private theorem wsMatrix_hadamard_bilin_eq (S : WeightScheme N) (i : Fin N)
    (a b : EuclideanSpace ℝ (BitString N)) :
    ∑ x, ∑ y, wsMatrix S x y * diffMatrix i x y * (|a.ofLp x| * |b.ofLp y|) =
      ∑ p ∈ S.R with p.1 i ≠ p.2 i,
        (S.w p / (√(S.wtFst p.1 + S.wtSnd p.1) * √(S.wtFst p.2 + S.wtSnd p.2))) *
          (|a.ofLp p.1| * |b.ofLp p.2| + |a.ofLp p.2| * |b.ofLp p.1|) := by
  classical
  let z : BitString N → ℝ := fun x => √(S.wtFst x + S.wtSnd x)
  have hΓdiff (x y : BitString N) :
      wsMatrix S x y * diffMatrix i x y * (|a.ofLp x| * |b.ofLp y|) =
      (∑ p ∈ S.R with p.1 i ≠ p.2 i ∧ p = (x, y),
        S.w p / (z p.1 * z p.2) * (|a.ofLp p.1| * |b.ofLp p.2|)) +
      (∑ p ∈ S.R with p.1 i ≠ p.2 i ∧ p = (y, x),
        S.w p / (z p.1 * z p.2) * (|a.ofLp p.2| * |b.ofLp p.1|)) := by
    by_cases hxi : x i ≠ y i
    · have hA1 : wsRaw S x y / (z x * z y) * (|a.ofLp x| * |b.ofLp y|) =
          ∑ p ∈ S.R with p.1 i ≠ p.2 i ∧ p = (x, y),
            S.w p / (z p.1 * z p.2) * (|a.ofLp p.1| * |b.ofLp p.2|) := by
        rw [wsRaw, Matrix.of_apply, sum_div, sum_mul]
        refine sum_congr ?_ fun p hp => ?_
        · ext p; simp only [mem_filter]
          exact ⟨fun h => ⟨h.1, ⟨by rw [h.2]; exact hxi, h.2⟩⟩, fun h => ⟨h.1, h.2.2⟩⟩
        · rw [(mem_filter.1 hp).2.2]
      have hA2 : wsRaw S y x / (z x * z y) * (|a.ofLp x| * |b.ofLp y|) =
          ∑ p ∈ S.R with p.1 i ≠ p.2 i ∧ p = (y, x),
            S.w p / (z p.1 * z p.2) * (|a.ofLp p.2| * |b.ofLp p.1|) := by
        rw [wsRaw, Matrix.of_apply, sum_div, sum_mul]
        refine sum_congr ?_ fun p hp => ?_
        · ext p; simp only [mem_filter]
          exact ⟨fun h => ⟨h.1, ⟨by rw [h.2]; exact hxi.symm, h.2⟩⟩, fun h => ⟨h.1, h.2.2⟩⟩
        · rw [(mem_filter.1 hp).2.2]; ring
      simp only [diffMatrix_apply, hxi, ne_eq, not_false_eq_true, ↓reduceIte, mul_one,
        wsMatrix, Matrix.of_apply, z, add_div, add_mul, hA1, hA2]
    · simp only [diffMatrix_apply, hxi, ne_eq, ↓reduceIte, mul_zero, zero_mul]
      symm
      rw [add_eq_zero_iff_of_nonneg (sum_nonneg fun p hp => by
        obtain ⟨hpR, _, _⟩ := mem_filter.1 hp
        have := S.w_nonneg p hpR
        positivity) (sum_nonneg fun p hp => by
        obtain ⟨hpR, _, _⟩ := mem_filter.1 hp
        have := S.w_nonneg p hpR
        positivity)]
      refine ⟨sum_eq_zero fun p hp => ?_, sum_eq_zero fun p hp => ?_⟩
      · obtain ⟨_, hne, hpq⟩ := mem_filter.1 hp
        rw [hpq] at hne; exact absurd hne hxi
      · obtain ⟨_, hne, hpq⟩ := mem_filter.1 hp
        rw [hpq] at hne; exact absurd (Ne.symm hne) hxi
  simp only [hΓdiff, sum_add_distrib]
  have hcollapse (f : BitString N × BitString N → ℝ) :
      (∑ x, ∑ y, ∑ p ∈ S.R with p.1 i ≠ p.2 i ∧ p = (x, y), f p) =
      ∑ p ∈ S.R with p.1 i ≠ p.2 i, f p := by
    rw [← Fintype.sum_prod_type (f := fun xy => ∑ p ∈ S.R with p.1 i ≠ p.2 i ∧ p = xy, f p)]
    have h_fiber := sum_fiberwise_of_maps_to (s := S.R.filter fun p => p.1 i ≠ p.2 i)
      (g := id) (t := univ) (fun _ _ => mem_univ _) f
    refine Eq.trans ?_ h_fiber
    refine sum_congr rfl fun _ _ => sum_congr (by ext; simp [id_eq, and_assoc]) fun _ _ => rfl
  have hf1 : ∑ x, ∑ y, ∑ p ∈ S.R with p.1 i ≠ p.2 i ∧ p = (x, y),
      S.w p / (z p.1 * z p.2) * (|a.ofLp p.1| * |b.ofLp p.2|) =
      ∑ p ∈ S.R with p.1 i ≠ p.2 i,
        S.w p / (z p.1 * z p.2) * (|a.ofLp p.1| * |b.ofLp p.2|) := hcollapse _
  have hf2 : ∑ x, ∑ y, ∑ p ∈ S.R with p.1 i ≠ p.2 i ∧ p = (y, x),
      S.w p / (z p.1 * z p.2) * (|a.ofLp p.2| * |b.ofLp p.1|) =
      ∑ p ∈ S.R with p.1 i ≠ p.2 i,
        S.w p / (z p.1 * z p.2) * (|a.ofLp p.2| * |b.ofLp p.1|) := by
    rw [sum_comm]
    exact hcollapse _
  rw [hf1, hf2, ← sum_add_distrib]
  refine sum_congr rfl fun p _ => by ring

private theorem wsMatrix_maxDiffNorm_le (S : WeightScheme N) {vA vB : ℝ}
    (hvA : 0 < vA) (hvB : 0 < vB)
    (hA : ∀ x ∈ S.R.image Prod.fst, ∀ i, S.loadFst x i ≤ vA * S.wtFst x)
    (hB : ∀ y ∈ S.R.image Prod.snd, ∀ i, S.loadSnd y i ≤ vB * S.wtSnd y) :
    maxDiffNorm (wsMatrix S) ≤ √(vA * vB) := by
  classical
  let z : BitString N → ℝ := fun x => √(S.wtFst x + S.wtSnd x)
  set c := √vB / √vA
  have hc : 0 < c := div_pos (Real.sqrt_pos.2 hvB) (Real.sqrt_pos.2 hvA)
  have hc_eq : c * vA = √(vA * vB) := by
    dsimp only [c]
    rw [Real.sqrt_mul hvA.le, div_mul_eq_mul_div]
    calc √vB * vA / √vA = √vB * (√vA * √vA) / √vA := by rw [Real.mul_self_sqrt hvA.le]
      _ = √vA * √vB := by field_simp [Real.sqrt_ne_zero'.2 hvA]
  have hc_eq' : vB / c = √(vA * vB) := by
    dsimp only [c]
    rw [Real.sqrt_mul hvA.le, div_div_eq_mul_div]
    calc vB * √vA / √vB = (√vB * √vB) * √vA / √vB := by rw [Real.mul_self_sqrt hvB.le]
      _ = √vA * √vB := by field_simp [Real.sqrt_ne_zero'.2 hvB]
  refine (maxDiffNorm_le_iff (Real.sqrt_nonneg _)).2 fun i => ?_
  refine Matrix.opNorm_toEuclideanCLM_le_of_inner _ (Real.sqrt_nonneg _) fun a b ha hb => ?_
  rw [Matrix.inner_toEuclideanCLM]
  simp only [dotProduct, Matrix.mulVec, mul_sum, Matrix.hadamard_apply]
  have hstep1 :
      ∑ x, ∑ y, a.ofLp x * (wsMatrix S x y * diffMatrix i x y * b.ofLp y) ≤
      ∑ p ∈ S.R with p.1 i ≠ p.2 i,
        (S.w p / (z p.1 * z p.2)) *
          (|a.ofLp p.1| * |b.ofLp p.2| + |a.ofLp p.2| * |b.ofLp p.1|) := by
    calc ∑ x, ∑ y, a.ofLp x * (wsMatrix S x y * diffMatrix i x y * b.ofLp y)
        ≤ ∑ x, ∑ y, wsMatrix S x y * diffMatrix i x y * (|a.ofLp x| * |b.ofLp y|) := by
          refine sum_le_sum fun x _ => sum_le_sum fun y _ => ?_
          have heq : a.ofLp x * (wsMatrix S x y * diffMatrix i x y * b.ofLp y) =
              wsMatrix S x y * diffMatrix i x y * (a.ofLp x * b.ofLp y) := by ring
          rw [heq]
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (wsMatrix_nonneg S x y) (by
            simp [diffMatrix]; split_ifs <;> norm_num))
          rw [← abs_mul]; exact le_abs_self _
      _ = ∑ p ∈ S.R with p.1 i ≠ p.2 i,
          (S.w p / (z p.1 * z p.2)) *
            (|a.ofLp p.1| * |b.ofLp p.2| + |a.ofLp p.2| * |b.ofLp p.1|) :=
          wsMatrix_hadamard_bilin_eq S i a b
  have hterm (p : BitString N × BitString N) (hp : p ∈ S.R.filter fun p => p.1 i ≠ p.2 i) :
      (S.w p / (z p.1 * z p.2)) *
        (|a.ofLp p.1| * |b.ofLp p.2| + |a.ofLp p.2| * |b.ofLp p.1|) ≤
      ((a.ofLp p.1 ^ 2 + b.ofLp p.1 ^ 2) * (c * S.u p i) / (S.wtFst p.1 + S.wtSnd p.1) +
        (a.ofLp p.2 ^ 2 + b.ofLp p.2 ^ 2) * (S.v p i / c) / (S.wtFst p.2 + S.wtSnd p.2)) /
        2 := by
    obtain ⟨hpR, hpi⟩ := mem_filter.1 hp
    rcases (S.w_nonneg p hpR).eq_or_lt with hw0 | hwpos
    · simp only [← hw0, zero_div, zero_mul]
      have hu0 := S.u_nonneg p hpR i hpi
      have hv0 := S.v_nonneg p hpR i hpi
      have := S.wtFst_nonneg p.1
      have := S.wtSnd_nonneg p.1
      have := S.wtFst_nonneg p.2
      have := S.wtSnd_nonneg p.2
      positivity
    · have hz1 : 0 < z p.1 := Real.sqrt_pos.2 (by
        have h1 : 0 < S.wtFst p.1 := lt_of_lt_of_le hwpos
          (single_le_sum (fun q hq => S.w_nonneg q (mem_filter.1 hq).1) (mem_filter.2 ⟨hpR, rfl⟩))
        linarith [S.wtSnd_nonneg p.1])
      have hz2 : 0 < z p.2 := Real.sqrt_pos.2 (by
        have h2 : 0 < S.wtSnd p.2 := lt_of_lt_of_le hwpos
          (single_le_sum (fun q hq => S.w_nonneg q (mem_filter.1 hq).1) (mem_filter.2 ⟨hpR, rfl⟩))
        linarith [S.wtFst_nonneg p.2])
      have hu0 := S.u_nonneg p hpR i hpi
      have hv0 := S.v_nonneg p hpR i hpi
      have hsq : S.w p ≤ √(c * S.u p i) * √(S.v p i / c) := by
        rw [← Real.sqrt_mul (mul_nonneg hc.le hu0)]
        have hid : (c * S.u p i) * (S.v p i / c) = S.u p i * S.v p i := by field_simp [hc.ne']
        rw [hid, Real.le_sqrt (S.w_nonneg p hpR) (mul_nonneg hu0 hv0)]
        exact S.sq_le p hpR i hpi
      set A1 := |a.ofLp p.1| * √(c * S.u p i) / z p.1
      set B2 := |b.ofLp p.2| * √(S.v p i / c) / z p.2
      set B1 := |b.ofLp p.1| * √(c * S.u p i) / z p.1
      set A2 := |a.ofLp p.2| * √(S.v p i / c) / z p.2
      have hm1 : A1 * B2 ≤ (A1 ^ 2 + B2 ^ 2) / 2 := by nlinarith [sq_nonneg (A1 - B2)]
      have hm2 : B1 * A2 ≤ (B1 ^ 2 + A2 ^ 2) / 2 := by nlinarith [sq_nonneg (B1 - A2)]
      have hpair :
          (S.w p / (z p.1 * z p.2)) *
            (|a.ofLp p.1| * |b.ofLp p.2| + |a.ofLp p.2| * |b.ofLp p.1|) ≤ A1 * B2 + B1 * A2 := by
        have heq : A1 * B2 + B1 * A2 =
            (√(c * S.u p i) * √(S.v p i / c) / (z p.1 * z p.2)) *
              (|a.ofLp p.1| * |b.ofLp p.2| + |a.ofLp p.2| * |b.ofLp p.1|) := by
          dsimp only [A1, B2, B1, A2]; ring
        rw [heq]
        refine mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right hsq (mul_nonneg hz1.le hz2.le))
          (add_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))
            (mul_nonneg (abs_nonneg _) (abs_nonneg _)))
      have hsqsum : (A1 ^ 2 + B2 ^ 2) / 2 + (B1 ^ 2 + A2 ^ 2) / 2 =
          ((a.ofLp p.1 ^ 2 + b.ofLp p.1 ^ 2) * (c * S.u p i) / (S.wtFst p.1 + S.wtSnd p.1) +
            (a.ofLp p.2 ^ 2 + b.ofLp p.2 ^ 2) * (S.v p i / c) /
              (S.wtFst p.2 + S.wtSnd p.2)) / 2 := by
        dsimp only [A1, B2, B1, A2, z]
        rw [div_pow, div_pow, div_pow, div_pow, mul_pow, mul_pow, mul_pow, mul_pow,
          Real.sq_sqrt (add_nonneg (S.wtFst_nonneg p.1) (S.wtSnd_nonneg p.1)),
          Real.sq_sqrt (add_nonneg (S.wtFst_nonneg p.2) (S.wtSnd_nonneg p.2)),
          Real.sq_sqrt (mul_nonneg hc.le hu0), Real.sq_sqrt (div_nonneg hv0 hc.le),
          sq_abs, sq_abs, sq_abs, sq_abs]
        ring
      linarith
  have hstep2 :
      ∑ p ∈ S.R with p.1 i ≠ p.2 i,
        (S.w p / (z p.1 * z p.2)) *
          (|a.ofLp p.1| * |b.ofLp p.2| + |a.ofLp p.2| * |b.ofLp p.1|) ≤ √(vA * vB) := by
    calc ∑ p ∈ S.R with p.1 i ≠ p.2 i,
          (S.w p / (z p.1 * z p.2)) *
            (|a.ofLp p.1| * |b.ofLp p.2| + |a.ofLp p.2| * |b.ofLp p.1|)
        ≤ ((∑ p ∈ S.R with p.1 i ≠ p.2 i,
              (a.ofLp p.1 ^ 2 + b.ofLp p.1 ^ 2) * (c * S.u p i) / (S.wtFst p.1 + S.wtSnd p.1)) +
            (∑ p ∈ S.R with p.1 i ≠ p.2 i,
              (a.ofLp p.2 ^ 2 + b.ofLp p.2 ^ 2) * (S.v p i / c) /
                (S.wtFst p.2 + S.wtSnd p.2))) / 2 := by
          rw [← sum_add_distrib, sum_div]
          exact sum_le_sum hterm
      _ ≤ (√(vA * vB) * ∑ x, (a.ofLp x ^ 2 + b.ofLp x ^ 2) *
              (S.wtFst x / (S.wtFst x + S.wtSnd x)) +
            √(vA * vB) * ∑ y, (a.ofLp y ^ 2 + b.ofLp y ^ 2) *
              (S.wtSnd y / (S.wtFst y + S.wtSnd y))) / 2 := by
          refine div_le_div_of_nonneg_right (add_le_add ?_ ?_) zero_le_two
          · rw [← sum_fiberwise_of_maps_to (s := S.R.filter fun p => p.1 i ≠ p.2 i)
              (g := Prod.fst) (t := univ) (fun _ _ => mem_univ _), mul_sum]
            refine sum_le_sum fun x _ => ?_
            have hxsum : ∑ p ∈ S.R.filter (fun p => p.1 i ≠ p.2 i) with p.1 = x,
                (a.ofLp p.1 ^ 2 + b.ofLp p.1 ^ 2) * (c * S.u p i) /
                  (S.wtFst p.1 + S.wtSnd p.1) =
                (a.ofLp x ^ 2 + b.ofLp x ^ 2) * (c * S.loadFst x i) /
                  (S.wtFst x + S.wtSnd x) := by
              simp only [WeightScheme.loadFst, mul_sum, sum_div]
              refine sum_congr ?_ fun p hp => ?_
              · ext p; simp only [mem_filter]; tauto
              · rw [(mem_filter.1 hp).2.2]
            rw [hxsum]
            by_cases hxfst : x ∈ S.R.image Prod.fst
            · calc (a.ofLp x ^ 2 + b.ofLp x ^ 2) * (c * S.loadFst x i) /
                    (S.wtFst x + S.wtSnd x)
                  ≤ (a.ofLp x ^ 2 + b.ofLp x ^ 2) * (c * (vA * S.wtFst x)) /
                      (S.wtFst x + S.wtSnd x) := by
                    refine div_le_div_of_nonneg_right
                      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hA x hxfst i) hc.le)
                        (add_nonneg (sq_nonneg _) (sq_nonneg _)))
                      (add_nonneg (S.wtFst_nonneg x) (S.wtSnd_nonneg x))
                _ = √(vA * vB) * ((a.ofLp x ^ 2 + b.ofLp x ^ 2) *
                      (S.wtFst x / (S.wtFst x + S.wtSnd x))) := by
                    rw [← mul_assoc c, hc_eq]; ring
            · have hl0 : S.loadFst x i = 0 := by
                refine sum_eq_zero fun p hp => ?_
                exact absurd (mem_image.2 ⟨p, (mem_filter.1 hp).1, (mem_filter.1 hp).2.2⟩) hxfst
              rw [hl0, mul_zero, mul_zero, zero_div]
              have := S.wtFst_nonneg x; have := S.wtSnd_nonneg x; positivity
          · rw [← sum_fiberwise_of_maps_to (s := S.R.filter fun p => p.1 i ≠ p.2 i)
              (g := Prod.snd) (t := univ) (fun _ _ => mem_univ _), mul_sum]
            refine sum_le_sum fun y _ => ?_
            have hysum : ∑ p ∈ S.R.filter (fun p => p.1 i ≠ p.2 i) with p.2 = y,
                (a.ofLp p.2 ^ 2 + b.ofLp p.2 ^ 2) * (S.v p i / c) /
                  (S.wtFst p.2 + S.wtSnd p.2) =
                (a.ofLp y ^ 2 + b.ofLp y ^ 2) * (S.loadSnd y i / c) /
                  (S.wtFst y + S.wtSnd y) := by
              simp only [WeightScheme.loadSnd, sum_div, mul_sum]
              refine sum_congr ?_ fun p hp => ?_
              · ext p; simp only [mem_filter]; tauto
              · rw [(mem_filter.1 hp).2.2]
            rw [hysum]
            by_cases hysnd : y ∈ S.R.image Prod.snd
            · calc (a.ofLp y ^ 2 + b.ofLp y ^ 2) * (S.loadSnd y i / c) /
                    (S.wtFst y + S.wtSnd y)
                  ≤ (a.ofLp y ^ 2 + b.ofLp y ^ 2) * (vB * S.wtSnd y / c) /
                      (S.wtFst y + S.wtSnd y) := by
                    refine div_le_div_of_nonneg_right
                      (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (hB y hysnd i) hc.le)
                        (add_nonneg (sq_nonneg _) (sq_nonneg _)))
                      (add_nonneg (S.wtFst_nonneg y) (S.wtSnd_nonneg y))
                _ = √(vA * vB) * ((a.ofLp y ^ 2 + b.ofLp y ^ 2) *
                      (S.wtSnd y / (S.wtFst y + S.wtSnd y))) := by
                    have hdiv : vB * S.wtSnd y / c = (vB / c) * S.wtSnd y := by ring
                    rw [hdiv, hc_eq']; ring
            · have hl0 : S.loadSnd y i = 0 := by
                refine sum_eq_zero fun p hp => ?_
                exact absurd (mem_image.2 ⟨p, (mem_filter.1 hp).1, (mem_filter.1 hp).2.2⟩) hysnd
              rw [hl0, zero_div, mul_zero, zero_div]
              have := S.wtFst_nonneg y; have := S.wtSnd_nonneg y; positivity
      _ = √(vA * vB) * (∑ x, (a.ofLp x ^ 2 + b.ofLp x ^ 2) *
            (S.wtFst x / (S.wtFst x + S.wtSnd x) + S.wtSnd x / (S.wtFst x + S.wtSnd x))) / 2 := by
          rw [← mul_add, ← sum_add_distrib]
          congr 1; congr 1
          refine sum_congr rfl fun x _ => by ring
      _ ≤ √(vA * vB) * (∑ x, (a.ofLp x ^ 2 + b.ofLp x ^ 2) * 1) / 2 := by
          refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
            (sum_le_sum fun x _ => mul_le_mul_of_nonneg_left ?_
              (add_nonneg (sq_nonneg _) (sq_nonneg _))) (Real.sqrt_nonneg _)) zero_le_two
          by_cases hs : S.wtFst x + S.wtSnd x = 0
          · simp [hs]
          · rw [← add_div, div_self hs]
      _ ≤ √(vA * vB) * (1 + 1) / 2 := by
          refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ?_
            (Real.sqrt_nonneg _)) zero_le_two
          simp only [mul_one, sum_add_distrib]
          have ha_sq : ∑ x, a.ofLp x ^ 2 ≤ 1 := by
            rw [← EuclideanSpace.real_norm_sq_eq]; exact pow_le_one₀ (norm_nonneg _) ha
          have hb_sq : ∑ x, b.ofLp x ^ 2 ≤ 1 := by
            rw [← EuclideanSpace.real_norm_sq_eq]; exact pow_le_one₀ (norm_nonneg _) hb
          exact add_le_add ha_sq hb_sq
      _ = √(vA * vB) := by ring
  exact hstep1.trans hstep2

/-- **Weighted bounds are at most the spectral adversary** (original proof /
[HoyerLeeSpalek2007]): any `WeightScheme` supported on `{(x, y) | P x ∧ P y ∧ f x ≠ f y}`
with `0 < S.weightSum` and `mA · loadFst x i ≤ wtFst x`, `mB · loadSnd y i ≤ wtSnd y` satisfies
`√(mA · mB) ≤ ADV(f)`. -/
theorem WeightScheme.le_spectralAdversary {α : Type*} {P : BitString N → Prop}
    {f : BitString N → α} (S : WeightScheme N) (hW : 0 < S.weightSum)
    (hS : ∀ p ∈ S.R, P p.1 ∧ P p.2 ∧ f p.1 ≠ f p.2)
    {mA mB : ℝ} (hmA : 0 ≤ mA) (hmB : 0 ≤ mB)
    (hA : ∀ x ∈ S.R.image Prod.fst, ∀ i, mA * S.loadFst x i ≤ S.wtFst x)
    (hB : ∀ y ∈ S.R.image Prod.snd, ∀ i, mB * S.loadSnd y i ≤ S.wtSnd y) :
    √(mA * mB) ≤ spectralAdversary P f := by
  rcases hmA.eq_or_lt with rfl | hmA_pos
  · simp [spectralAdversary_nonneg]
  rcases hmB.eq_or_lt with rfl | hmB_pos
  · simp [spectralAdversary_nonneg]
  let Γ := wsMatrix S
  have hsym : Γ.IsSymm := wsMatrix_isSymm S
  have hnonneg : ∀ x y, 0 ≤ Γ x y := wsMatrix_nonneg S
  have hΓ : IsAdversaryMatrix P f Γ := wsMatrix_isAdversary S hS
  have hnorm1 : 1 ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ := wsMatrix_opNorm_ge_one S hW
  have hmax : maxDiffNorm Γ ≤ √(mA⁻¹ * mB⁻¹) := wsMatrix_maxDiffNorm_le S
    (inv_pos.2 hmA_pos) (inv_pos.2 hmB_pos)
    (fun x hx i => by rw [inv_mul_eq_div, le_div_iff₀' hmA_pos]; exact hA x hx i)
    (fun y hy i => by rw [inv_mul_eq_div, le_div_iff₀' hmB_pos]; exact hB y hy i)
  have hm_pos : 0 < maxDiffNorm Γ := by
    by_contra hle
    have hm0 : maxDiffNorm Γ = 0 := le_antisymm (not_lt.1 hle) (maxDiffNorm_nonneg Γ)
    have hΓ0 := eq_zero_of_maxDiffNorm_eq_zero hΓ hm0
    rw [hΓ0, map_zero, norm_zero] at hnorm1
    linarith
  have hsqrt : maxDiffNorm Γ ≤ (√(mA * mB))⁻¹ := by
    rwa [← mul_inv, Real.sqrt_inv] at hmax
  have hinv : √(mA * mB) ≤ (maxDiffNorm Γ)⁻¹ := by
    have hpos : 0 < √(mA * mB) := Real.sqrt_pos.2 (mul_pos hmA_pos hmB_pos)
    exact (le_inv_comm₀ hm_pos hpos).1 hsqrt
  calc √(mA * mB) ≤ (maxDiffNorm Γ)⁻¹ := hinv
    _ = 1 / maxDiffNorm Γ := (one_div _).symm
    _ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ / maxDiffNorm Γ :=
        div_le_div_of_nonneg_right hnorm1 hm_pos.le
    _ ≤ spectralAdversary P f := _root_.Cslib.Quantum.le_spectralAdversary hsym hnonneg hΓ

/-- **Hamming-distance barrier for nonnegative adversary matrices** (property-testing / distance
barrier noted in [HoyerLeeSpalek2007], Section 7.2): if `0 ≤ Γ` and every nonzero entry
`(x, y)` has Hamming distance at least `k`, then `k · ‖Γ‖ ≤ N · maxDiffNorm Γ`. -/
theorem mul_opNorm_le_mul_maxDiffNorm_of_hammingDist_ge
    {Γ : Matrix (BitString N) (BitString N) ℝ} (hnonneg : ∀ x y, 0 ≤ Γ x y) {k : ℕ}
    (hk : ∀ x y, Γ x y ≠ 0 → k ≤ #{i : Fin N | x i ≠ y i}) :
    (k : ℝ) * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ ≤ N * maxDiffNorm Γ := by
  rcases Nat.eq_zero_or_pos k with rfl | hk_pos
  · simp only [Nat.cast_zero, zero_mul]
    exact mul_nonneg (Nat.cast_nonneg _) (maxDiffNorm_nonneg Γ)
  have hk0 : (0 : ℝ) < k := Nat.cast_pos.2 hk_pos
  have hbilin : ∀ u v : EuclideanSpace ℝ (BitString N), ‖u‖ ≤ 1 → ‖v‖ ≤ 1 →
      (k : ℝ) * inner ℝ u (Matrix.toEuclideanCLM (𝕜 := ℝ) Γ v) ≤ N * maxDiffNorm Γ := by
    intro u v hu hv
    have huPos := Matrix.norm_absVec_le hu
    have hvPos := Matrix.norm_absVec_le hv
    calc (k : ℝ) * inner ℝ u (Matrix.toEuclideanCLM (𝕜 := ℝ) Γ v)
        ≤ (k : ℝ) * inner ℝ (Matrix.absVec u)
            (Matrix.toEuclideanCLM (𝕜 := ℝ) Γ (Matrix.absVec v)) :=
          mul_le_mul_of_nonneg_left (Matrix.inner_toEuclideanCLM_le_absVec hnonneg u v) hk0.le
      _ ≤ ∑ i : Fin N, inner ℝ (Matrix.absVec u) (Matrix.toEuclideanCLM (𝕜 := ℝ)
            (Γ.hadamard (diffMatrix i)) (Matrix.absVec v)) := by
          have hrhs : ∑ i : Fin N, inner ℝ (Matrix.absVec u) (Matrix.toEuclideanCLM (𝕜 := ℝ)
                (Γ.hadamard (diffMatrix i)) (Matrix.absVec v)) =
              ∑ x, ∑ y, Γ x y * (#{i : Fin N | x i ≠ y i} : ℝ) *
                |u.ofLp x| * |v.ofLp y| := by
            simp only [Matrix.inner_toEuclideanCLM, dotProduct, Matrix.mulVec, mul_sum,
              Matrix.absVec_apply, Matrix.hadamard_apply]
            rw [sum_comm]
            refine sum_congr rfl fun x _ => ?_
            rw [sum_comm]
            refine sum_congr rfl fun y _ => ?_
            have hdiff_sum : (∑ i : Fin N, diffMatrix i x y) = (#{i : Fin N | x i ≠ y i} : ℝ) := by
              rw [Finset.card_filter]; simp [diffMatrix]
            simp only [mul_assoc, ← hdiff_sum, mul_sum, sum_mul]
            refine sum_congr rfl fun i _ => by ring
          have hlhs : (k : ℝ) * inner ℝ (Matrix.absVec u)
                (Matrix.toEuclideanCLM (𝕜 := ℝ) Γ (Matrix.absVec v)) =
              ∑ x, ∑ y, (k : ℝ) * (Γ x y * |u.ofLp x| * |v.ofLp y|) := by
            rw [Matrix.inner_toEuclideanCLM]
            simp only [dotProduct, Matrix.mulVec, mul_sum, Matrix.absVec_apply]
            refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => by ring
          rw [hlhs, hrhs]
          refine sum_le_sum fun x _ => sum_le_sum fun y _ => ?_
          by_cases hxy0 : Γ x y = 0
          · simp [hxy0]
          · have hkx : (k : ℝ) ≤ #{i : Fin N | x i ≠ y i} := Nat.cast_le.2 (hk x y hxy0)
            nlinarith [mul_nonneg (mul_nonneg (hnonneg x y) (abs_nonneg (u.ofLp x)))
              (abs_nonneg (v.ofLp y))]
      _ ≤ ∑ _i : Fin N, maxDiffNorm Γ := by
          refine sum_le_sum fun i _ => ?_
          calc inner ℝ (Matrix.absVec u) (Matrix.toEuclideanCLM (𝕜 := ℝ)
                (Γ.hadamard (diffMatrix i)) (Matrix.absVec v))
              ≤ ‖Matrix.absVec u‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℝ)
                (Γ.hadamard (diffMatrix i)) (Matrix.absVec v)‖ := real_inner_le_norm _ _
            _ ≤ 1 * (‖Matrix.toEuclideanCLM (𝕜 := ℝ) (Γ.hadamard (diffMatrix i))‖ *
                  ‖Matrix.absVec v‖) :=
                mul_le_mul huPos (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _) zero_le_one
            _ ≤ maxDiffNorm Γ * 1 := by
                rw [one_mul]
                exact mul_le_mul (norm_toEuclideanCLM_hadamard_le_maxDiffNorm Γ i) hvPos
                  (norm_nonneg _) (maxDiffNorm_nonneg Γ)
            _ = maxDiffNorm Γ := mul_one _
      _ = N * maxDiffNorm Γ := by simp
  have hnorm_le := Matrix.opNorm_toEuclideanCLM_le_of_inner Γ
    (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (maxDiffNorm_nonneg _)) hk0.le)
    fun u v hu hv => (le_div_iff₀ hk0).2 (by rw [mul_comm]; exact hbilin u v hu hv)
  rw [mul_comm]
  exact (le_div_iff₀ hk0).1 hnorm_le

/-- **Hamming-distance barrier on `ADV(f)`**: if every distinguishing pair `(x, y)` of valid
inputs has Hamming distance at least `k > 0`, then `ADV(f) ≤ N / k`. -/
theorem spectralAdversary_le_div_of_hammingDist_ge {α : Type*} {P : BitString N → Prop}
    {f : BitString N → α} {k : ℕ} (hk0 : 0 < k)
    (hk : ∀ x y, P x → P y → f x ≠ f y → k ≤ #{i : Fin N | x i ≠ y i}) :
    spectralAdversary P f ≤ (N : ℝ) / k := by
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.2 hk0
  refine csSup_le ⟨0, 0, Matrix.isSymm_zero, fun _ _ => le_rfl,
    fun _ _ h => (h rfl).elim, by simp⟩ ?_
  rintro r ⟨Γ, -, hnonneg, hΓ, rfl⟩
  by_cases hm0 : maxDiffNorm Γ = 0
  · simp only [hm0, div_zero]; positivity
  · have hm : 0 < maxDiffNorm Γ := lt_of_le_of_ne (maxDiffNorm_nonneg Γ) (Ne.symm hm0)
    have hb := mul_opNorm_le_mul_maxDiffNorm_of_hammingDist_ge hnonneg fun x y hxy0 =>
      let ⟨hx, hy, hf⟩ := hΓ x y hxy0
      hk x y hx hy hf
    rw [div_le_div_iff₀ hm hk_pos]
    linarith

end HierarchyAndBarriers

end Cslib.Quantum
