/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.NoncommRing

/-!
# Corrections, copies and reward transport for transition matrices

Let `C` be the transition matrix of a finite Markov chain that may stop (its rows sum to at most
one), and let `e` be a reward collected when it stops. The expected reward `p` from each state
solves `(1 - C) p = e`; when `C` is nilpotent, `p = (1 - C)⁻¹ e`. For the time-layered
configuration graph of a randomized machine, `p` is the vector of acceptance probabilities.

This file develops the exact algebra of a hierarchy that shrinks the entries of `C` while keeping
`p` recoverable, following the OpenAI preprint (2026-09-23), Section 4, idea 2 and the deterministic
part of idea 4 in issue #474 [OpenAI2026LogSpace]. The estimates that choose the corrections and
the copies (factorial truncation, detectors) are not part of this file.

* **Correction.** For any matrix `E`, the *corrected* matrix `D = C - E + E C` satisfies
  `1 - D = (1 + E) (1 - C)` (`one_add_mul_one_sub_eq_one_sub`, a ring identity). So the same `p`
  solves `(1 - D) p = (1 + E) e` (`Matrix.one_sub_correction_mulVec`): the correction moves
  transition weight into the reward `e + E e`. When `1 + E` is invertible, for example when `E` is
  strictly upper triangular, `(1 - D)⁻¹ (e + E e) = (1 - C)⁻¹ e`
  (`Matrix.inv_one_sub_correction_mulVec`). If `E ≥ 0` and the rows of `C` sum to at most one,
  the rows of `D` sum to at most as much (`Matrix.correction_mulVec_one_le`).
* **Copies.** A vertex `x` is replaced by copies `(x, i)`, weighted by `r i x`, and an entry
  `D x y` is split among the copies of `y` in proportions `s x y j` (`Matrix.copySplit`).
  If the weighted proportions sum to one on the support of `D`, the projection
  `Matrix.copyWeight r` intertwines the two matrices: `copySplit r s D * copyWeight r =
  copyWeight r * D` (`Matrix.copySplit_mul_copyWeight`).
* **Reward transport.** Iterating, a sequence of stages with transition matrices `C l`,
  corrections `E l` and projections `P l` satisfying `C (l + 1) * P l = P l * D l` carries the
  cumulative projection `Matrix.copyProjection` and the transported reward
  `Matrix.rewardTransport`, with `C l * Pc l = Pc l - B l * (1 - C 0)`
  (`Matrix.mul_copyProjection`). Hence the stage-`l` reward `W l = B l e` equals
  `Pc l p - C l Pc l p` (`Matrix.rewardTransport_mulVec`). At a vertex `z l` reached from `z 0`
  by primary copies only, the transported reward underestimates `p (z 0)` by at most the row
  sum of `C l` (`Matrix.sub_rewardTransport_mulVec_mem_Icc`), so by at most `|A l| * ε l` when
  the entries of `C l` are at most `ε l` and its nonzero columns lie in `A l`
  (`Matrix.sub_rewardTransport_mulVec_le_card_mul`). With the paper's per-stage rates (entries
  shrink by `2 ^ (c + 1)`, active columns at most double) this is the stage bound
  `0 ≤ p (z 0) - W l (z l) ≤ n / 2 ^ (c l)` (`Matrix.sub_rewardTransport_mulVec_le_pow`).

## Main definitions

* `Matrix.IsStrictUpperTriangular`: entries vanish unless the row index is below the column index.
* `Matrix.copySplit`, `Matrix.copyWeight`: a copy step and its weighted projection.
* `Matrix.copyProjection`, `Matrix.rewardTransport`: cumulative projections and rewards of a
  sequence of stages.

## Main results

* `one_add_mul_one_sub_eq_one_sub`: `(1 + e) (1 - c) = 1 - (c - e + e c)` in any ring.
* `Matrix.one_sub_correction_mulVec`, `Matrix.inv_one_sub_correction_mulVec`: the expected reward
  of `C` is the expected corrected reward of `C - E + E C`.
* `Matrix.IsStrictUpperTriangular.det_one_add`: `det (1 + E) = 1` for strictly upper triangular
  `E`.
* `Matrix.correction_mulVec_one_le`: nonnegative corrections do not increase row sums.
* `Matrix.copySplit_mul_copyWeight`: a copy step intertwines with its projection.
* `Matrix.mul_copyProjection`, `Matrix.rewardTransport_mulVec`: the reward transport identity.
* `Matrix.rewardTransport_mulVec_nonneg`, `Matrix.rewardTransport_mulVec_le`: the stage rewards
  lie between `0` and the projected solution.
* `Matrix.sub_rewardTransport_mulVec_mem_Icc`, `Matrix.sub_rewardTransport_mulVec_le_card_mul`,
  `Matrix.sub_rewardTransport_mulVec_le_pow`: the transported reward is a lower bound with error
  controlled by the last transition matrix.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Section 4 (preprint, not peer reviewed)
-/

public section

open Finset

/-- **The correction factorization.** In any ring, correcting `c` by `e` to `c - e + e * c`
factors `1 - (c - e + e * c)` as `(1 + e) * (1 - c)` [OpenAI2026LogSpace, Section 4]. -/
theorem one_add_mul_one_sub_eq_one_sub {R : Type*} [Ring R] (c e : R) :
    (1 + e) * (1 - c) = 1 - (c - e + e * c) := by
  noncomm_ring

namespace Matrix

section Triangular

variable {V R : Type*}

/-- A square matrix is *strictly upper triangular* when its entry at `(i, j)` vanishes unless
`i < j`. For the time-layered transition matrices of a machine, ordered by time, this says that
every transition moves strictly forward. -/
@[expose] def IsStrictUpperTriangular [LT V] [Zero R] (M : Matrix V V R) : Prop :=
  ∀ ⦃i j⦄, ¬ i < j → M i j = 0

namespace IsStrictUpperTriangular

variable [Preorder V] {M N : Matrix V V R}

/-- A strictly upper triangular matrix is upper triangular. -/
theorem isUpperTriangular [Zero R] (h : M.IsStrictUpperTriangular) : M.IsUpperTriangular :=
  fun _ _ hji => h (lt_asymm hji)

theorem add [AddZeroClass R] (hM : M.IsStrictUpperTriangular) (hN : N.IsStrictUpperTriangular) :
    (M + N).IsStrictUpperTriangular := fun i j hij => by
  simp only [Matrix.add_apply, hM hij, hN hij, add_zero]

theorem neg [SubtractionMonoid R] (hM : M.IsStrictUpperTriangular) :
    (-M).IsStrictUpperTriangular := fun i j hij => by
  simp only [Matrix.neg_apply, hM hij, neg_zero]

theorem sub [SubtractionMonoid R] (hM : M.IsStrictUpperTriangular)
    (hN : N.IsStrictUpperTriangular) : (M - N).IsStrictUpperTriangular := fun i j hij => by
  simp only [Matrix.sub_apply, hM hij, hN hij, sub_zero]

theorem mul [Fintype V] [NonUnitalNonAssocSemiring R] (hM : M.IsStrictUpperTriangular)
    (hN : N.IsStrictUpperTriangular) : (M * N).IsStrictUpperTriangular := fun i j hij => by
  refine Finset.sum_eq_zero fun k _ => ?_
  change M i k * N k j = 0
  by_cases hik : i < k
  · rw [hN fun hkj => hij (hik.trans hkj), mul_zero]
  · rw [hM hik, zero_mul]

/-- `1 + E` has determinant one when `E` is strictly upper triangular. -/
theorem det_one_add {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] [CommRing R]
    {E : Matrix V V R} (h : E.IsStrictUpperTriangular) : (1 + E).det = 1 := by
  have hT : (1 + E).IsUpperTriangular := fun i j (hji : j < i) => by
    rw [Matrix.add_apply, one_apply_ne (ne_of_lt hji).symm, h.isUpperTriangular hji, add_zero]
  rw [det_of_isUpperTriangular hT]
  exact Finset.prod_eq_one fun i _ => by
    rw [Matrix.add_apply, one_apply_eq, h (lt_irrefl i), add_zero]

end IsStrictUpperTriangular

end Triangular

section Correction

variable {V R : Type*} [Fintype V]

/-- **Corrections preserve the expected reward.** Correcting `C` to `C - E + E * C` turns the
equation `(1 - C) p = e` into `(1 - D) p = (1 + E) e` for the same `p`: the weight removed from
the transitions reappears in the reward [OpenAI2026LogSpace, Section 4]. -/
theorem one_sub_correction_mulVec [DecidableEq V] [Ring R] (C E : Matrix V V R) (p : V → R) :
    (1 - (C - E + E * C)) *ᵥ p = (1 + E) *ᵥ ((1 - C) *ᵥ p) := by
  rw [mulVec_mulVec, one_add_mul_one_sub_eq_one_sub]

/-- **The corrected inverse.** When `1 + E` is invertible, the expected reward
`(1 - C)⁻¹ e` of `C` equals the expected reward of the corrected matrix `C - E + E * C` with the
corrected reward `e + E e`. -/
theorem inv_one_sub_correction_mulVec [DecidableEq V] [CommRing R] {C E : Matrix V V R}
    (hE : IsUnit (1 + E).det) (e : V → R) :
    (1 - (C - E + E * C))⁻¹ *ᵥ (e + E *ᵥ e) = (1 - C)⁻¹ *ᵥ e := by
  have h : (1 - (C - E + E * C))⁻¹ * (1 + E) = (1 - C)⁻¹ := by
    rw [← one_add_mul_one_sub_eq_one_sub, mul_inv_rev,
      nonsing_inv_mul_cancel_right (1 + E) (1 - C)⁻¹ hE]
  rw [← h, ← mulVec_mulVec, add_mulVec, one_mulVec]

/-- The corrected inverse for a strictly upper triangular correction. -/
theorem IsStrictUpperTriangular.inv_one_sub_correction_mulVec [DecidableEq V] [LinearOrder V]
    [CommRing R] {C E : Matrix V V R} (hE : E.IsStrictUpperTriangular) (e : V → R) :
    (1 - (C - E + E * C))⁻¹ *ᵥ (e + E *ᵥ e) = (1 - C)⁻¹ *ᵥ e :=
  Matrix.inv_one_sub_correction_mulVec (by rw [hE.det_one_add]; exact isUnit_one) e

/-- The row sums of a corrected matrix: `(C - E + E C) 1 = C 1 - E (1 - C 1)`. -/
theorem correction_mulVec_one [Ring R] (C E : Matrix V V R) :
    (C - E + E * C) *ᵥ 1 = C *ᵥ 1 - E *ᵥ (1 - C *ᵥ 1) := by
  rw [add_mulVec, sub_mulVec, ← mulVec_mulVec, mulVec_sub]
  abel

/-- An entrywise nonnegative matrix maps nonnegative vectors to nonnegative vectors. -/
theorem mulVec_nonneg {m n : Type*} [Fintype n] [Semiring R] [PartialOrder R] [IsOrderedRing R]
    {M : Matrix m n R} (hM : ∀ i j, 0 ≤ M i j) {v : n → R} (hv : 0 ≤ v) : 0 ≤ M *ᵥ v :=
  fun i => Finset.sum_nonneg fun j _ => mul_nonneg (hM i j) (hv j)

/-- An entrywise nonnegative matrix whose rows sum to at most one maps vectors with entries at
most one to vectors with entries at most one. -/
theorem mulVec_le_one {m n : Type*} [Fintype n] [Semiring R] [PartialOrder R] [IsOrderedRing R]
    {M : Matrix m n R} (hM : ∀ i j, 0 ≤ M i j) (hM1 : M *ᵥ 1 ≤ 1) {v : n → R}
    (hv : v ≤ 1) :
    M *ᵥ v ≤ 1 := fun i =>
  le_trans (Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hv j) (hM i j)) (hM1 i)

/-- **Corrections do not increase row sums.** If `E ≥ 0` and the rows of `C` sum to at most one,
then each row of `C - E + E C` sums to at most the corresponding row of `C`. This says nothing
about the signs of the entries of `C - E + E C`; their nonnegativity depends on how `E` is
chosen [OpenAI2026LogSpace, Lemma 4.4]. -/
theorem correction_mulVec_one_le [Ring R] [PartialOrder R] [IsOrderedRing R]
    {C E : Matrix V V R} (hE : ∀ i j, 0 ≤ E i j) (hC : C *ᵥ 1 ≤ 1) :
    (C - E + E * C) *ᵥ 1 ≤ C *ᵥ 1 := by
  rw [correction_mulVec_one]
  exact sub_le_self _ (mulVec_nonneg hE (sub_nonneg.mpr hC))

end Correction

section Copy

variable {V ι R : Type*}

/-- **A copy step.** Each vertex `x` gets copies `(x, i)` with row weights `r i x`, and the entry
`D x y` is split among the copies `(y, j)` of its target in proportions `s x y j`. In the
preprint the proportions depend only on the size of `D x y`, and the copies beyond a primary one
are activated only at targets where the correction was suppressed
[OpenAI2026LogSpace, Section 4.4]. -/
@[expose] def copySplit [Mul R] (r : ι → V → R) (s : V → V → ι → R) (D : Matrix V V R) :
    Matrix (V × ι) (V × ι) R :=
  of fun a b => r a.2 a.1 * D a.1 b.1 * s a.1 b.1 b.2

/-- The *copy projection* from copies to their parents, weighted by `r`: the copy `(x, i)` maps
to `x` with weight `r i x`. -/
@[expose] def copyWeight [DecidableEq V] [Zero R] (r : ι → V → R) : Matrix (V × ι) V R :=
  of fun a z => if a.1 = z then r a.2 a.1 else 0

@[simp]
theorem copyWeight_mulVec [Fintype V] [DecidableEq V] [NonUnitalNonAssocSemiring R]
    (r : ι → V → R) (v : V → R) (a : V × ι) :
    (copyWeight r *ᵥ v) a = r a.2 a.1 * v a.1 := by
  simp [copyWeight, mulVec, dotProduct, ite_mul]

/-- A copy with weight one projects to its parent exactly. -/
theorem copyWeight_apply_of_eq_one [DecidableEq V] [Semiring R] {r : ι → V → R} {x : V}
    {i : ι} (h : r i x = 1) (w : V) : copyWeight r (x, i) w = if w = x then 1 else 0 := by
  simp [copyWeight, h, eq_comm]

/-- **Copies intertwine with their projection.** If, on every nonzero entry `D x y`, the
proportions `s x y j` weighted by `r j y` sum to one, then splitting `D` into copies and
projecting back agrees with projecting first: `copySplit r s D * copyWeight r =
copyWeight r * D` [OpenAI2026LogSpace, Proposition 4.5]. -/
theorem copySplit_mul_copyWeight [Fintype V] [DecidableEq V] [Fintype ι] [Semiring R]
    {r : ι → V → R} {s : V → V → ι → R} {D : Matrix V V R}
    (hs : ∀ x y, D x y ≠ 0 → ∑ j, s x y j * r j y = 1) :
    copySplit r s D * copyWeight r = copyWeight r * D := by
  ext ⟨x, i⟩ z
  have hL : (copySplit r s D * copyWeight r) (x, i) z = r i x * D x z * ∑ j, s x z j * r j z := by
    rw [Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_eq_single z fun y hy => ?_,
      Finset.mul_sum]
    · simp [copySplit, copyWeight, mul_assoc]
    · simp [copyWeight, hy]
  have hR : (copyWeight r * D) (x, i) z = r i x * D x z := by
    rw [Matrix.mul_apply, Fintype.sum_eq_single x fun y hy => ?_]
    · simp [copyWeight]
    · simp [copyWeight, Ne.symm hy]
  rw [hL, hR]
  by_cases hD : D x z = 0
  · simp [hD]
  · rw [hs x z hD, mul_one]

theorem copySplit_nonneg [Semiring R] [PartialOrder R] [IsOrderedRing R] {r : ι → V → R}
    {s : V → V → ι → R} {D : Matrix V V R} (hr : ∀ i x, 0 ≤ r i x)
    (hs : ∀ x y j, 0 ≤ s x y j) (hD : ∀ x y, 0 ≤ D x y) (a b : V × ι) :
    0 ≤ copySplit r s D a b :=
  mul_nonneg (mul_nonneg (hr _ _) (hD _ _)) (hs _ _ _)

/-- **Copies keep row sums at most one** when the weights lie in `[0, 1]`, `D` is nonnegative
with row sums at most one, and the proportions of each entry sum to at most one. Together with
`Matrix.copySplit_nonneg` this makes the copy step substochastic. -/
theorem copySplit_mulVec_one_le [Fintype V] [Fintype ι] [Semiring R] [PartialOrder R]
    [IsOrderedRing R] {r : ι → V → R} {s : V → V → ι → R} {D : Matrix V V R}
    (hr0 : ∀ i x, 0 ≤ r i x) (hr1 : ∀ i x, r i x ≤ 1) (hs1 : ∀ x y, ∑ j, s x y j ≤ 1)
    (hD0 : ∀ x y, 0 ≤ D x y) (hD1 : D *ᵥ 1 ≤ 1) : copySplit r s D *ᵥ 1 ≤ 1 := by
  rintro ⟨x, i⟩
  have hrow : ∑ b : V × ι, copySplit r s D (x, i) b ≤ r i x * ∑ y, D x y := by
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_le_sum fun y _ => ?_
    simp only [copySplit, of_apply, ← Finset.mul_sum]
    exact mul_le_of_le_one_right (mul_nonneg (hr0 i x) (hD0 x y)) (hs1 x y)
  have hDx : ∑ y, D x y ≤ 1 := by simpa [mulVec, dotProduct] using hD1 x
  simpa [mulVec, dotProduct] using
    (hrow.trans (mul_le_of_le_one_right (hr0 i x) hDx)).trans (hr1 i x)

end Copy

section Hierarchy

variable {V : ℕ → Type*} [∀ l, Fintype (V l)] [∀ l, DecidableEq (V l)] {R : Type*}

/-- **The cumulative projection** of a sequence of stages with projections
`P l : Matrix (V (l + 1)) (V l) R`: the product `P (l - 1) * ⋯ * P 0`, from stage `l` to
stage `0`. -/
@[expose] def copyProjection [Semiring R] (P : ∀ l, Matrix (V (l + 1)) (V l) R) :
    ∀ l, Matrix (V l) (V 0) R
  | 0 => 1
  | l + 1 => P l * copyProjection P l

/-- **The transported reward matrix** of a sequence of stages with projections `P l` and
corrections `E l`: `B (l + 1) = P l * (1 + E l) * B l`, starting from `B 0 = 1`. Applied to the
initial reward `e`, it gives the stage-`l` reward `B l e`. -/
@[expose] def rewardTransport [Semiring R] (P : ∀ l, Matrix (V (l + 1)) (V l) R)
    (E : ∀ l, Matrix (V l) (V l) R) : ∀ l, Matrix (V l) (V 0) R
  | 0 => 1
  | l + 1 => P l * (1 + E l) * rewardTransport P E l

variable {C E : ∀ l, Matrix (V l) (V l) R} {P : ∀ l, Matrix (V (l + 1)) (V l) R}

/-- **The reward transport identity.** If each stage's transition matrix intertwines with the
corrected matrix of the previous stage, `C (l + 1) * P l = P l * (C l - E l + E l * C l)`, then
`C l * Pc l = Pc l - B l * (1 - C 0)` for the cumulative projection `Pc` and the transported
reward matrix `B` [OpenAI2026LogSpace, Proposition 4.7]. -/
theorem mul_copyProjection [Ring R]
    (h : ∀ l, C (l + 1) * P l = P l * (C l - E l + E l * C l)) (l : ℕ) :
    C l * copyProjection P l = copyProjection P l - rewardTransport P E l * (1 - C 0) := by
  induction l with
  | zero => simp [copyProjection, rewardTransport]
  | succ l ih =>
    have hD : C l - E l + E l * C l = 1 - (1 + E l) * (1 - C l) := by
      rw [one_add_mul_one_sub_eq_one_sub, sub_sub_cancel]
    have hB : (1 - C l) * copyProjection P l = rewardTransport P E l * (1 - C 0) := by
      rw [Matrix.sub_mul, Matrix.one_mul, ih, sub_sub_cancel]
    calc C (l + 1) * copyProjection P (l + 1)
        = P l * (C l - E l + E l * C l) * copyProjection P l := by
          rw [copyProjection, ← Matrix.mul_assoc, h]
      _ = P l * copyProjection P l - P l * (1 + E l) * ((1 - C l) * copyProjection P l) := by
          rw [hD]
          simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
            Matrix.mul_assoc]
      _ = copyProjection P (l + 1) - rewardTransport P E (l + 1) * (1 - C 0) := by
          rw [hB]
          simp only [copyProjection, rewardTransport, Matrix.mul_assoc]

/-- **The transported reward.** If `p` solves `(1 - C 0) p = e`, the stage-`l` reward is
`B l e = Pc l p - C l (Pc l p)`: the projected solution minus what the remaining transitions
still carry [OpenAI2026LogSpace, Proposition 4.7]. -/
theorem rewardTransport_mulVec [Ring R]
    (h : ∀ l, C (l + 1) * P l = P l * (C l - E l + E l * C l)) {p e : V 0 → R}
    (hp : (1 - C 0) *ᵥ p = e) (l : ℕ) :
    rewardTransport P E l *ᵥ e =
      copyProjection P l *ᵥ p - C l *ᵥ (copyProjection P l *ᵥ p) := by
  rw [mulVec_mulVec, mul_copyProjection h, sub_mulVec, ← mulVec_mulVec, hp, sub_sub_cancel]

/-- The stage rewards are updated by adding the correction's contribution and projecting:
`W (l + 1) = P l (W l + E l W l)`. -/
theorem rewardTransport_succ_mulVec [Semiring R] (e : V 0 → R) (l : ℕ) :
    rewardTransport P E (l + 1) *ᵥ e =
      P l *ᵥ (rewardTransport P E l *ᵥ e + E l *ᵥ (rewardTransport P E l *ᵥ e)) := by
  rw [rewardTransport, ← mulVec_mulVec, ← mulVec_mulVec, add_mulVec, one_mulVec]

/-- Along *primary copies* `z l`, whose rows of `P l` are unit vectors, the cumulative projection
reads off the original coordinate. -/
theorem copyProjection_mulVec_primary [Semiring R] {z : ∀ l, V l}
    (hz : ∀ l w, P l (z (l + 1)) w = if w = z l then 1 else 0) (p : V 0 → R) (l : ℕ) :
    (copyProjection P l *ᵥ p) (z l) = p (z 0) := by
  induction l with
  | zero => simp [copyProjection]
  | succ l ih =>
    rw [copyProjection, ← mulVec_mulVec]
    simp [mulVec, dotProduct, hz, ite_mul, ← ih]

section Order

variable [Ring R] [PartialOrder R] [IsOrderedRing R]

private theorem one_apply_nonneg {n : Type*} [DecidableEq n] (i j : n) :
    (0 : R) ≤ (1 : Matrix n n R) i j := by
  rw [Matrix.one_apply]; split_ifs <;> simp

private theorem mul_nonneg_entries {m n o : Type*} [Fintype n] {A : Matrix m n R}
    {B : Matrix n o R} (hA : ∀ i j, 0 ≤ A i j) (hB : ∀ i j, 0 ≤ B i j) (i : m) (k : o) :
    0 ≤ (A * B) i k :=
  Finset.sum_nonneg fun j _ => mul_nonneg (hA i j) (hB j k)

theorem copyProjection_nonneg (hP : ∀ l i j, 0 ≤ P l i j) (l : ℕ) :
    ∀ i j, 0 ≤ copyProjection P l i j := by
  induction l with
  | zero => exact one_apply_nonneg
  | succ l ih => exact mul_nonneg_entries (hP l) ih

/-- The cumulative projection of substochastic projections is substochastic. -/
theorem copyProjection_mulVec_one_le (hP : ∀ l i j, 0 ≤ P l i j) (hP1 : ∀ l, P l *ᵥ 1 ≤ 1)
    (l : ℕ) : copyProjection P l *ᵥ 1 ≤ 1 := by
  induction l with
  | zero => simp [copyProjection]
  | succ l ih =>
    rw [copyProjection, ← mulVec_mulVec]
    exact mulVec_le_one (hP l) (hP1 l) ih

theorem rewardTransport_nonneg (hP : ∀ l i j, 0 ≤ P l i j) (hE : ∀ l i j, 0 ≤ E l i j)
    (l : ℕ) : ∀ i j, 0 ≤ rewardTransport P E l i j := by
  induction l with
  | zero => exact one_apply_nonneg
  | succ l ih =>
    exact mul_nonneg_entries (mul_nonneg_entries (hP l)
      (fun i j => add_nonneg (one_apply_nonneg i j) (hE l i j))) ih

/-- The stage rewards are nonnegative when the projections, the corrections and the initial reward
are [OpenAI2026LogSpace, Proposition 4.7]. -/
theorem rewardTransport_mulVec_nonneg (hP : ∀ l i j, 0 ≤ P l i j) (hE : ∀ l i j, 0 ≤ E l i j)
    {e : V 0 → R} (he : 0 ≤ e) (l : ℕ) : 0 ≤ rewardTransport P E l *ᵥ e :=
  mulVec_nonneg (rewardTransport_nonneg hP hE l) he

variable (hP : ∀ l i j, 0 ≤ P l i j) (hP1 : ∀ l, P l *ᵥ 1 ≤ 1)
  (hC : ∀ l i j, 0 ≤ C l i j) (hstep : ∀ l, C (l + 1) * P l = P l * (C l - E l + E l * C l))
  {p e : V 0 → R}
  (hp : (1 - C 0) *ᵥ p = e) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
include hP hP1 hC hstep hp hp0 hp1

/-- The stage rewards are bounded by the projected solution, hence by one. For the lower bound
see `Matrix.rewardTransport_mulVec_nonneg`. -/
theorem rewardTransport_mulVec_le (l : ℕ) :
    rewardTransport P E l *ᵥ e ≤ copyProjection P l *ᵥ p ∧
      copyProjection P l *ᵥ p ≤ 1 := by
  have hPc0 : 0 ≤ copyProjection P l *ᵥ p := mulVec_nonneg (copyProjection_nonneg hP l) hp0
  refine ⟨?_, mulVec_le_one (copyProjection_nonneg hP l)
    (copyProjection_mulVec_one_le hP hP1 l) hp1⟩
  rw [rewardTransport_mulVec hstep hp]
  exact sub_le_self _ (mulVec_nonneg (hC l) hPc0)

/-- **The stage error.** Along primary copies `z l`, the stage-`l` reward underestimates the
solution at `z 0` by at most the row sum of `C l` at `z l`
[OpenAI2026LogSpace, Proposition 4.7]. -/
theorem sub_rewardTransport_mulVec_mem_Icc {z : ∀ l, V l}
    (hz : ∀ l w, P l (z (l + 1)) w = if w = z l then 1 else 0) (l : ℕ) :
    p (z 0) - (rewardTransport P E l *ᵥ e) (z l) ∈ Set.Icc 0 (∑ y, C l (z l) y) := by
  have hPc0 : 0 ≤ copyProjection P l *ᵥ p := mulVec_nonneg (copyProjection_nonneg hP l) hp0
  have hPc1 : copyProjection P l *ᵥ p ≤ 1 :=
    (rewardTransport_mulVec_le hP hP1 hC hstep hp hp0 hp1 l).2
  rw [rewardTransport_mulVec hstep hp, Pi.sub_apply, copyProjection_mulVec_primary hz,
    sub_sub_cancel]
  exact ⟨mulVec_nonneg (hC l) hPc0 _, Finset.sum_le_sum fun y _ =>
    mul_le_of_le_one_right (hC l _ y) (hPc1 y)⟩

/-- **The stage error, by counting.** If the entries of `C l` are at most `ε` and its nonzero
columns lie in `A`, the stage-`l` reward along primary copies underestimates the solution by at
most `|A| ε`. -/
theorem sub_rewardTransport_mulVec_le_card_mul {z : ∀ l, V l}
    (hz : ∀ l w, P l (z (l + 1)) w = if w = z l then 1 else 0) (l : ℕ) {ε : R}
    (hε : ∀ x y, C l x y ≤ ε) {A : Finset (V l)} (hA : ∀ x y, C l x y ≠ 0 → y ∈ A) :
    p (z 0) - (rewardTransport P E l *ᵥ e) (z l) ≤ A.card • ε := by
  refine (sub_rewardTransport_mulVec_mem_Icc hP hP1 hC hstep hp hp0 hp1 hz l).2.trans ?_
  rw [← Finset.sum_subset (Finset.subset_univ A) fun y _ hy => by_contra fun h => hy (hA _ y h)]
  exact Finset.sum_le_card_nsmul _ _ _ fun y _ => hε _ y

end Order

/-- **The stage bound.** If the entries of `C l` are at most `(2 ^ (c + 1))⁻¹ ^ l` and its
nonzero columns lie in a set of at most `2 ^ l * n` vertices, then along primary copies
`0 ≤ p (z 0) - W l (z l) ≤ n * (2 ^ c)⁻¹ ^ l`. With `n` the number of vertices of stage `0`,
this is the preprint's bound `|V₀| 2 ^ (-(H - 1) l)` for `H = c + 1`
[OpenAI2026LogSpace, Proposition 4.7]. -/
theorem sub_rewardTransport_mulVec_le_pow [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (hP : ∀ l i j, 0 ≤ P l i j) (hP1 : ∀ l, P l *ᵥ 1 ≤ 1) (hC : ∀ l i j, 0 ≤ C l i j)
    (hstep : ∀ l, C (l + 1) * P l = P l * (C l - E l + E l * C l)) {p e : V 0 → R}
    (hp : (1 - C 0) *ᵥ p = e) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {z : ∀ l, V l}
    (hz : ∀ l w, P l (z (l + 1)) w = if w = z l then 1 else 0) {c n : ℕ}
    (hε : ∀ l x y, C l x y ≤ ((2 : R) ^ (c + 1))⁻¹ ^ l) (A : ∀ l, Finset (V l))
    (hA : ∀ l x y, C l x y ≠ 0 → y ∈ A l) (hAn : ∀ l, (A l).card ≤ 2 ^ l * n)
    (l : ℕ) :
    0 ≤ p (z 0) - (rewardTransport P E l *ᵥ e) (z l) ∧
      p (z 0) - (rewardTransport P E l *ᵥ e) (z l) ≤ n * ((2 : R) ^ c)⁻¹ ^ l := by
  refine ⟨(sub_rewardTransport_mulVec_mem_Icc hP hP1 hC hstep hp hp0 hp1 hz l).1, ?_⟩
  refine (sub_rewardTransport_mulVec_le_card_mul hP hP1 hC hstep hp hp0 hp1 hz l (hε l)
    (hA l)).trans ?_
  rw [nsmul_eq_mul]
  calc ((A l).card : R) * ((2 : R) ^ (c + 1))⁻¹ ^ l
      ≤ (2 ^ l * n : ℕ) * ((2 : R) ^ (c + 1))⁻¹ ^ l :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hAn l)
          (pow_nonneg (inv_nonneg.mpr (pow_nonneg zero_le_two _)) _)
    _ = n * ((2 : R) ^ c)⁻¹ ^ l := by
        have h2 : (2 : R) ^ l ≠ 0 := pow_ne_zero _ two_ne_zero
        push_cast
        rw [pow_succ, mul_inv, mul_pow, inv_pow (2 : R), mul_comm ((2 : R) ^ l), mul_assoc,
          ← mul_assoc ((2 : R) ^ l), mul_comm ((2 : R) ^ l), mul_assoc _ ((2 : R) ^ l),
          mul_inv_cancel₀ h2, mul_one]

end Hierarchy

end Matrix
