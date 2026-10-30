/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Foundations.LinearAlgebra.Matrix.CorrectionHierarchy
public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Topology.Algebra.Order.Floor

/-!
# Factorial truncation of cutoff corrections

Let `C` be a strictly upper triangular transition matrix with nonnegative entries at most `f`
and rows summing to at most one. A *cutoff correction* chooses the correction `E` of
`Matrix.one_sub_correction_mulVec` entrywise from the corrected input,
`E x y = φ y ((C + E C) x y)`, where each cutoff `φ y` is monotone, `L`-Lipschitz and leaves at
least `θ f` behind: `0 ≤ φ y t ≤ max (t - θ f) 0`. In the OpenAI preprint (2026-09-23), idea 3 in
issue #474, `φ y t = f Q (t / f) g y` for a smooth ramp `Q` and a column multiplier `g`
[OpenAI2026LogSpace, Section 4.1].

The equation is a recursion along the order of the columns, so it has exactly one solution
`Matrix.cutoffCorrectionFix φ C`, reached by iterating `Matrix.cutoffCorrection φ C` from zero
`card V` times (`Matrix.cutoffCorrection_fix`, `Matrix.eq_cutoffCorrectionFix`). The point of
the estimate is that far fewer iterations suffice, independently of the size of `V`: after `k`
iterations every entry is within `f e^(1 / θ) (L / θ)^k / k!` of the fixed point
(`Matrix.cutoffCorrectionFix_sub_iter_le`).

The proof counts chains. In a fixed row, every positive entry of the fixed point leaves a residual
at least `θ f`, and the residuals of a row sum to at most one, so the number `m` of positive
entries in the row satisfies `m θ f ≤ 1`. Unrolling the recursion `k` times along that row
expresses the error as a sum over increasing chains of `k` of these entries, each weighted by at
most `(L f)^k`; there are at most `m.choose k ≤ m^k / k! ≤ (θ f)^(-k) / k!` of them.

For the finite correction `E = E k`, the corrected matrix `C - E + E C` is nonnegative
(`Matrix.cutoffCorrection_residual_nonneg`), and in a column whose cutoff leaves at most `θ₂ f`
behind its entries are at most `θ₂ f` plus the truncation error
(`Matrix.cutoffCorrection_residual_le`). Since `x ^ k / k!` tends to zero, a number of iterations
depending only on `θ`, `L` and the target accuracy suffices (`Matrix.exists_factorial_bound_le`).

## Main definitions

* `Matrix.cutoffCorrection`: one step `F ↦ φ y ((C + F C) x y)` of the recursion.
* `Matrix.cutoffCorrectionIter`: its `k`-th iterate from zero.
* `Matrix.cutoffCorrectionFix`: its unique fixed point.

## Main results

* `Matrix.cutoffCorrection_fix`, `Matrix.eq_cutoffCorrectionFix`: existence and uniqueness of the
  fixed point, for strictly upper triangular `C`.
* `Matrix.cutoffCorrectionIter_le_fix`: the iterates increase towards the fixed point.
* `Matrix.cutoffCorrectionFix_sub_iter_le`: **factorial truncation**, the bound
  `E* - E k ≤ f e^(1 / θ) (L / θ)^k / k!`.
* `Matrix.cutoffCorrection_residual_nonneg`, `Matrix.cutoffCorrection_residual_le`: the corrected
  matrix of a finite iterate is nonnegative, with small entries in fully corrected columns.
* `Matrix.exists_factorial_bound_le`: a uniform number of iterations reaches any accuracy.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Lemma 4.1 and Lemma 4.4 (preprint, not peer reviewed). The estimate is of Picard type: compare
  the factorial bound for Picard iterates of Lipschitz ODEs.
-/

public section

open Finset

namespace Matrix

variable {V R : Type*} [Fintype V]

section Recursion

variable [NonUnitalNonAssocSemiring R]

/-- **One step of the cutoff correction recursion**: the matrix with entry
`φ y ((C + F C) x y)` at `(x, y)`. -/
@[expose] def cutoffCorrection (φ : V → R → R) (C F : Matrix V V R) : Matrix V V R :=
  of fun x y => φ y ((C + F * C) x y)

/-- The `k`-th iterate of `Matrix.cutoffCorrection φ C` from the zero matrix. -/
@[expose] def cutoffCorrectionIter (φ : V → R → R) (C : Matrix V V R) (k : ℕ) : Matrix V V R :=
  (cutoffCorrection φ C)^[k] 0

/-- The *cutoff correction* of `C`: the iterate after `card V` steps, which is the unique fixed
point of `Matrix.cutoffCorrection φ C` when `C` is strictly upper triangular. -/
@[expose] def cutoffCorrectionFix (φ : V → R → R) (C : Matrix V V R) : Matrix V V R :=
  cutoffCorrectionIter φ C (Fintype.card V)

variable {φ : V → R → R} {C : Matrix V V R}

theorem cutoffCorrectionIter_succ (k : ℕ) :
    cutoffCorrectionIter φ C (k + 1) = cutoffCorrection φ C (cutoffCorrectionIter φ C k) :=
  Function.iterate_succ_apply' _ _ _

variable [LinearOrder V]

/-- The entry `(x, y)` of a correction step depends only on the entries `(x, z)` with `z < y`. -/
private theorem cutoffCorrection_congr (hC : C.IsStrictUpperTriangular) {F G : Matrix V V R}
    {x y : V} (h : ∀ z < y, F x z = G x z) :
    cutoffCorrection φ C F x y = cutoffCorrection φ C G x y := by
  simp only [cutoffCorrection, of_apply, Matrix.add_apply, Matrix.mul_apply]
  congr 2
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases hz : z < y
  · rw [h z hz]
  · rw [hC hz, mul_zero, mul_zero]

private theorem card_filter_lt_lt {y z : V} (hzy : z < y) :
    #{w | w < z} < #{w | w < y} :=
  Finset.card_lt_card <| Finset.ssubset_iff_of_subset
    (fun w hw => by simp only [mem_filter, mem_univ, true_and] at hw ⊢; exact hw.trans hzy)
    |>.mpr ⟨z, by simpa using hzy, by simp⟩

/-- The iterates are stationary at `(x, y)` from the `(#{z | z < y} + 1)`-th on. -/
private theorem cutoffCorrectionIter_succ_apply (hC : C.IsStrictUpperTriangular) (k : ℕ) :
    ∀ x y : V, #{z | z < y} < k →
      cutoffCorrectionIter φ C (k + 1) x y = cutoffCorrectionIter φ C k x y := by
  induction k with
  | zero => intro x y h; exact absurd h (Nat.not_lt_zero _)
  | succ k ih =>
    intro x y h
    rw [cutoffCorrectionIter_succ (k := k + 1)]
    conv_rhs => rw [cutoffCorrectionIter_succ]
    exact cutoffCorrection_congr hC fun z hz =>
      ih x z ((card_filter_lt_lt hz).trans_le (Nat.lt_succ_iff.mp h))

/-- **Existence of the cutoff correction**: `Matrix.cutoffCorrectionFix φ C` is a fixed point of
the recursion when `C` is strictly upper triangular [OpenAI2026LogSpace, Lemma 4.1]. -/
theorem cutoffCorrection_fix (hC : C.IsStrictUpperTriangular) :
    cutoffCorrection φ C (cutoffCorrectionFix φ C) = cutoffCorrectionFix φ C := by
  ext x y
  rw [cutoffCorrectionFix, ← cutoffCorrectionIter_succ]
  refine cutoffCorrectionIter_succ_apply hC _ x y (Finset.card_lt_card ?_)
  exact Finset.ssubset_iff_of_subset (Finset.subset_univ _) |>.mpr ⟨y, mem_univ _, by simp⟩

/-- **Uniqueness of the cutoff correction**: every fixed point of the recursion is
`Matrix.cutoffCorrectionFix φ C` when `C` is strictly upper triangular
[OpenAI2026LogSpace, Lemma 4.1]. -/
theorem eq_cutoffCorrectionFix (hC : C.IsStrictUpperTriangular) {F : Matrix V V R}
    (hF : cutoffCorrection φ C F = F) : F = cutoffCorrectionFix φ C := by
  ext x y
  induction y using WellFoundedLT.induction with
  | ind y ih =>
    rw [← hF, ← cutoffCorrection_fix hC]
    exact cutoffCorrection_congr hC ih

end Recursion

section Bounds

variable [LinearOrder V] {φ : V → ℝ → ℝ} {C : Matrix V V ℝ} {f θ L : ℝ}

omit [Fintype V] in
/-- Counting increasing chains by rank: summing a nonnegative `g` of the rank within `S` over the
members of `S` below `y` is at most summing `g` over the ranks below the rank of `y`. -/
private theorem sum_rank_le (S : Finset V) (y : V) {g : ℕ → ℝ} (hg : ∀ j, 0 ≤ g j) :
    ∑ z ∈ S.filter (· < y), g #(S.filter (· < z)) ≤
      ∑ j ∈ range #(S.filter (· < y)), g j := by
  have hlt : ∀ {a b : V}, a ∈ S → a < b → #(S.filter (· < a)) < #(S.filter (· < b)) :=
    fun {a b} ha hab => Finset.card_lt_card <| Finset.ssubset_iff_of_subset
      (fun w hw => by simp only [mem_filter] at hw ⊢; exact ⟨hw.1, hw.2.trans hab⟩)
      |>.mpr ⟨a, by simp [ha, hab], by simp⟩
  have hinj : Set.InjOn (fun z => #(S.filter (· < z))) (S.filter (· < y) : Set V) := by
    intro a ha b hb hab
    simp only [coe_filter, Set.mem_ofPred_eq] at ha hb
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact (hlt ha.1 h).ne hab
    · exact (hlt hb.1 h).ne hab.symm
  rw [← Finset.sum_image (f := g) hinj]
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun j hj => ?_) fun j _ _ => hg j
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hj
  simp only [mem_filter] at hz
  exact Finset.mem_range.mpr (hlt hz.1 hz.2)

variable (hC : C.IsStrictUpperTriangular) (hC0 : ∀ x y, 0 ≤ C x y) (hCf : ∀ x y, C x y ≤ f)
  (hC1 : C *ᵥ 1 ≤ 1) (hφ0 : ∀ y t, 0 ≤ φ y t) (hφθ : ∀ y t, φ y t ≤ max (t - θ * f) 0)
  (hφm : ∀ y, Monotone (φ y)) (hφL : ∀ y s t, s ≤ t → φ y t - φ y s ≤ L * (t - s))

section Monotone

omit [LinearOrder V] in
include hC0 hφm in
private theorem cutoffCorrection_mono {F G : Matrix V V ℝ} (hFG : ∀ x y, F x y ≤ G x y)
    (x y : V) : cutoffCorrection φ C F x y ≤ cutoffCorrection φ C G x y := by
  refine hφm y ?_
  simp only [Matrix.add_apply, Matrix.mul_apply]
  exact add_le_add_right (Finset.sum_le_sum fun z _ =>
    mul_le_mul_of_nonneg_right (hFG x z) (hC0 z y)) _

omit [LinearOrder V] in
include hφ0 in
theorem cutoffCorrectionIter_nonneg (k : ℕ) (x y : V) : 0 ≤ cutoffCorrectionIter φ C k x y := by
  cases k with
  | zero => simp [cutoffCorrectionIter]
  | succ k => rw [cutoffCorrectionIter_succ]; exact hφ0 _ _

omit [LinearOrder V] in
include hC0 hφ0 hφm in
/-- The iterates increase. -/
theorem cutoffCorrectionIter_le_succ (k : ℕ) (x y : V) :
    cutoffCorrectionIter φ C k x y ≤ cutoffCorrectionIter φ C (k + 1) x y := by
  induction k generalizing x y with
  | zero => exact cutoffCorrectionIter_nonneg hφ0 1 x y
  | succ k ih =>
    rw [cutoffCorrectionIter_succ, cutoffCorrectionIter_succ (k := k + 1)]
    exact cutoffCorrection_mono hC0 hφm ih x y

include hC hC0 hφ0 hφm in
/-- **The iterates increase towards the fixed point** [OpenAI2026LogSpace, Lemma 4.1]. -/
theorem cutoffCorrectionIter_le_fix (k : ℕ) (x y : V) :
    cutoffCorrectionIter φ C k x y ≤ cutoffCorrectionFix φ C x y := by
  induction k generalizing x y with
  | zero => exact cutoffCorrectionIter_nonneg hφ0 _ x y
  | succ k ih =>
    rw [cutoffCorrectionIter_succ, ← cutoffCorrection_fix hC]
    exact cutoffCorrection_mono hC0 hφm ih x y

end Monotone

omit [LinearOrder V] in
/-- The input `(C + F C) x y` of a correction step is nonnegative. -/
private theorem correctionInput_nonneg (hC0 : ∀ x y, 0 ≤ C x y) {F : Matrix V V ℝ}
    (hF : ∀ x y, 0 ≤ F x y) (x y : V) : 0 ≤ (C + F * C) x y :=
  add_nonneg (hC0 x y) (Finset.sum_nonneg fun z _ => mul_nonneg (hF x z) (hC0 z y))

omit [Fintype V] [LinearOrder V] in
include hφθ in
/-- A cutoff never exceeds its nonnegative input. -/
private theorem cutoff_le_self (hθf : 0 ≤ θ * f) (y : V) {t : ℝ} (ht : 0 ≤ t) : φ y t ≤ t :=
  (hφθ y t).trans (max_le (by linarith) ht)

omit [Fintype V] [LinearOrder V] in
include hφθ in
/-- A positive cutoff leaves at least `θ f` behind. -/
private theorem le_sub_cutoff_of_pos (y : V) {t : ℝ} (h : 0 < φ y t) : θ * f ≤ t - φ y t := by
  have h1 := hφθ y t
  have h2 : 0 < t - θ * f := by
    by_contra hneg
    rw [max_eq_right (by linarith)] at h1
    linarith
  rw [max_eq_left h2.le] at h1
  linarith

include hC in
private theorem fix_apply (x y : V) :
    cutoffCorrectionFix φ C x y = φ y ((C + cutoffCorrectionFix φ C * C) x y) := by
  conv_lhs => rw [← cutoffCorrection_fix hC]
  rfl

section Row

variable (x : V)

/-- The positive entries of row `x` of the fixed point. -/
private noncomputable abbrev support : Finset V := {z | cutoffCorrectionFix φ C x z ≠ 0}

include hC hC0 hC1 hφ0 hφθ in
/-- In each row, the fixed point has at most `1 / (θ f)` positive entries: each leaves a
residual at least `θ f`, and the residuals of a row sum to at most one. -/
private theorem card_support_mul_le (hθf : 0 ≤ θ * f) :
    (#(support (φ := φ) (C := C) x) : ℝ) * (θ * f) ≤ 1 := by
  set E := cutoffCorrectionFix φ C
  have hE0 : ∀ i j, 0 ≤ E i j := cutoffCorrectionIter_nonneg hφ0 _
  have hEfix : ∀ y, E x y = φ y ((C + E * C) x y) := fix_apply hC x
  have hres : ∀ y, (C - E + E * C) x y = (C + E * C) x y - E x y := fun y => by
    simp only [Matrix.add_apply, Matrix.sub_apply]; ring
  have hres0 : ∀ y, 0 ≤ (C - E + E * C) x y := fun y => by
    rw [hres, hEfix y, sub_nonneg]
    exact cutoff_le_self hφθ hθf y (correctionInput_nonneg hC0 hE0 x y)
  have hrow : ∑ y, (C - E + E * C) x y ≤ 1 := by
    simpa [mulVec, dotProduct] using (correction_mulVec_one_le hE0 hC1 x).trans (hC1 x)
  calc (#(support (φ := φ) (C := C) x) : ℝ) * (θ * f)
      = ∑ y ∈ support (φ := φ) (C := C) x, θ * f := by rw [sum_const, nsmul_eq_mul]
    _ ≤ ∑ y ∈ support (φ := φ) (C := C) x, (C - E + E * C) x y := by
        refine Finset.sum_le_sum fun y hy => ?_
        have hpos : 0 < φ y ((C + E * C) x y) := by
          rw [← hEfix y]
          exact lt_of_le_of_ne (hE0 x y) (Ne.symm (by simpa using hy))
        rw [hres, hEfix y]
        exact le_sub_cutoff_of_pos hφθ y hpos
    _ ≤ ∑ y, (C - E + E * C) x y :=
        Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) fun y _ _ => hres0 y
    _ ≤ 1 := hrow

/-- A sum `∑ z, F x z * C z y` only sees the members of `support x` below `y`, when `F` vanishes
outside the support. -/
private theorem sum_mul_eq_sum_support (hC : C.IsStrictUpperTriangular) {F : Matrix V V ℝ}
    (hF : ∀ z, cutoffCorrectionFix φ C x z = 0 → F x z = 0) (y : V) :
    ∑ z, F x z * C z y = ∑ z ∈ (support (φ := φ) (C := C) x).filter (· < y), F x z * C z y := by
  refine (Finset.sum_subset (subset_univ _) fun z _ hz => ?_).symm
  simp only [mem_filter, mem_univ, true_and, not_and_or, not_not] at hz
  rcases hz with hz | hz
  · rw [hF z hz, zero_mul]
  · rw [hC hz, mul_zero]

include hC hC0 hCf hφ0 hφθ in
/-- The entries of the fixed point grow at most geometrically along the support of a row. -/
private theorem fix_le_pow (hf : 0 ≤ f) (hθf : 0 ≤ θ * f) (y : V) :
    cutoffCorrectionFix φ C x y ≤
      f * (1 + f) ^ #((support (φ := φ) (C := C) x).filter (· < y)) := by
  set E := cutoffCorrectionFix φ C
  have hE0 : ∀ i j, 0 ≤ E i j := cutoffCorrectionIter_nonneg hφ0 _
  induction y using WellFoundedLT.induction with
  | ind y ih =>
    set S := support (φ := φ) (C := C) x
    have hEfix : E x y = φ y ((C + E * C) x y) := fix_apply hC x y
    have hsum : ∑ z, E x z * C z y = ∑ z ∈ S.filter (· < y), E x z * C z y :=
      sum_mul_eq_sum_support x hC (fun _ h => h) y
    calc E x y ≤ (C + E * C) x y := by
          rw [hEfix]; exact cutoff_le_self hφθ hθf y (correctionInput_nonneg hC0 hE0 x y)
      _ = C x y + ∑ z ∈ S.filter (· < y), E x z * C z y := by
          rw [Matrix.add_apply, Matrix.mul_apply, hsum]
      _ ≤ f + ∑ z ∈ S.filter (· < y), f * (1 + f) ^ #(S.filter (· < z)) * f := by
          refine add_le_add (hCf x y) (Finset.sum_le_sum fun z hz => ?_)
          exact mul_le_mul (ih z (mem_filter.mp hz).2) (hCf z y) (hC0 z y) (by positivity)
      _ = f + f * f * ∑ z ∈ S.filter (· < y), (1 + f) ^ #(S.filter (· < z)) := by
          rw [Finset.mul_sum]; congr 1; exact Finset.sum_congr rfl fun z _ => by ring
      _ ≤ f + f * f * ∑ j ∈ range #(S.filter (· < y)), (1 + f) ^ j := by
          gcongr
          exact sum_rank_le S y fun j => by positivity
      _ = f * (1 + f) ^ #(S.filter (· < y)) := by
          have := geom_sum_mul_add f #(S.filter (· < y))
          rw [add_comm f 1] at this
          linear_combination f * this

include hC hC0 hCf hφ0 hφθ hφm hφL in
/-- The iteration error along a row is bounded by counting increasing chains in its support. -/
private theorem fix_sub_iter_le_choose (hf : 0 ≤ f) (hθf : 0 ≤ θ * f) (hL : 0 ≤ L) (k : ℕ)
    (y : V) : cutoffCorrectionFix φ C x y - cutoffCorrectionIter φ C k x y ≤
      f * (1 + f) ^ #(support (φ := φ) (C := C) x) * (L * f) ^ k *
        (#((support (φ := φ) (C := C) x).filter (· < y))).choose k := by
  set E := cutoffCorrectionFix φ C
  set S := support (φ := φ) (C := C) x
  have hE0 : ∀ i j, 0 ≤ E i j := cutoffCorrectionIter_nonneg hφ0 _
  have hM : ∀ y, E x y ≤ f * (1 + f) ^ #S := fun y =>
    (fix_le_pow hC hC0 hCf hφ0 hφθ x hf hθf y).trans <| mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by linarith) (card_le_card (filter_subset _ _))) hf
  induction k generalizing y with
  | zero =>
    simpa using (sub_le_self _ (cutoffCorrectionIter_nonneg hφ0 0 x y)).trans (hM y)
  | succ k ih =>
    set F := cutoffCorrectionIter φ C k
    have hFE : ∀ z, F x z ≤ E x z := cutoffCorrectionIter_le_fix hC hC0 hφ0 hφm k x
    have hEfix : E x y = φ y ((C + E * C) x y) := fix_apply hC x y
    have hsum : ∑ z, (E - F) x z * C z y = ∑ z ∈ S.filter (· < y), (E - F) x z * C z y :=
      sum_mul_eq_sum_support x hC (fun z hz => by
        change E x z = 0 at hz
        rw [Matrix.sub_apply, hz, sub_eq_zero]
        exact le_antisymm (cutoffCorrectionIter_nonneg (C := C) hφ0 k x z) (hz ▸ hFE z)) y
    have hdiff : (C + E * C) x y - (C + F * C) x y = ∑ z, (E - F) x z * C z y := by
      simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.sub_apply, sub_mul,
        Finset.sum_sub_distrib]
      ring
    have hle : (C + F * C) x y ≤ (C + E * C) x y := by
      rw [← sub_nonneg, hdiff]
      exact Finset.sum_nonneg fun z _ =>
        mul_nonneg (by rw [Matrix.sub_apply, sub_nonneg]; exact hFE z) (hC0 z y)
    calc E x y - cutoffCorrectionIter φ C (k + 1) x y
        = φ y ((C + E * C) x y) - φ y ((C + F * C) x y) := by
          rw [hEfix, cutoffCorrectionIter_succ]; rfl
      _ ≤ L * ∑ z ∈ S.filter (· < y), (E - F) x z * C z y := by
          rw [← hsum, ← hdiff]
          exact hφL y _ _ hle
      _ ≤ L * ∑ z ∈ S.filter (· < y),
            f * (1 + f) ^ #S * (L * f) ^ k * (#(S.filter (· < z))).choose k * f := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun z _ => ?_) hL
          rw [Matrix.sub_apply]
          exact mul_le_mul (ih z) (hCf z y) (hC0 z y) (by positivity)
      _ = f * (1 + f) ^ #S * (L * f) ^ (k + 1) *
            ∑ z ∈ S.filter (· < y), ((#(S.filter (· < z))).choose k : ℝ) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun z _ => by ring
      _ ≤ f * (1 + f) ^ #S * (L * f) ^ (k + 1) *
            ∑ j ∈ range #(S.filter (· < y)), (j.choose k : ℝ) := by
          gcongr
          exact sum_rank_le S y (g := fun j => (j.choose k : ℝ)) fun j => by positivity
      _ = f * (1 + f) ^ #S * (L * f) ^ (k + 1) * (#(S.filter (· < y))).choose (k + 1) := by
          -- the hockey-stick identity `∑ j ∈ Icc k n, j.choose k = (n + 1).choose (k + 1)`
          congr 1
          rcases hn : #(S.filter (· < y)) with _ | n
          · simp
          · rw [← Nat.sum_Icc_choose, Nat.cast_sum]
            refine (Finset.sum_subset (fun j hj => ?_) fun j hj hjn => ?_).symm
            · simp only [mem_Icc, mem_range] at hj ⊢; omega
            · simp only [mem_Icc, mem_range, not_and_or, not_le] at hj hjn
              rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]

end Row

include hC hC0 hCf hC1 hφ0 hφθ hφm hφL in
/-- **Factorial truncation.** After `k` iterations of the cutoff correction recursion, every entry
is within `f e^(1 / θ) (L / θ)^k / k!` of the fixed point, uniformly in the size of `V`
[OpenAI2026LogSpace, Lemma 4.1]. -/
theorem cutoffCorrectionFix_sub_iter_le (hf : 0 < f) (hθ : 0 < θ) (hL : 0 ≤ L) (k : ℕ)
    (x y : V) : cutoffCorrectionFix φ C x y - cutoffCorrectionIter φ C k x y ≤
      f * Real.exp (1 / θ) * (L / θ) ^ k / k.factorial := by
  have hθf : 0 ≤ θ * f := by positivity
  set S := support (φ := φ) (C := C) x
  set m := #S
  have hm : (m : ℝ) * f ≤ 1 / θ := by
    rw [le_div_iff₀ hθ]
    nlinarith [card_support_mul_le hC hC0 hC1 hφ0 hφθ x hθf]
  have hr : #(S.filter (· < y)) ≤ m := card_le_card (filter_subset _ _)
  refine (fix_sub_iter_le_choose hC hC0 hCf hφ0 hφθ hφm hφL x hf.le hθf hL k y).trans ?_
  have hexp : (1 + f) ^ m ≤ Real.exp (1 / θ) := by
    calc (1 + f) ^ m ≤ Real.exp f ^ m := by
          gcongr; linarith [Real.add_one_le_exp f]
      _ = Real.exp (m * f) := by rw [← Real.exp_nat_mul]
      _ ≤ Real.exp (1 / θ) := Real.exp_le_exp.mpr hm
  have hchoose : ((#(S.filter (· < y))).choose k : ℝ) ≤ (m : ℝ) ^ k / k.factorial :=
    (Nat.choose_le_pow_div k _).trans (by gcongr)
  have hLf : (L * f) ^ k * ((m : ℝ) ^ k / k.factorial) ≤ (L / θ) ^ k / k.factorial := by
    rw [← mul_div_assoc, ← mul_pow]
    gcongr
    calc L * f * m = L * (m * f) := by ring
      _ ≤ L * (1 / θ) := by gcongr
      _ = L / θ := by ring
  calc f * (1 + f) ^ m * (L * f) ^ k * ((#(S.filter (· < y))).choose k : ℝ)
      ≤ f * Real.exp (1 / θ) * ((L * f) ^ k * ((m : ℝ) ^ k / k.factorial)) := by
        rw [mul_assoc (f * (1 + f) ^ m)]
        gcongr
    _ ≤ f * Real.exp (1 / θ) * ((L / θ) ^ k / k.factorial) := by gcongr
    _ = f * Real.exp (1 / θ) * (L / θ) ^ k / k.factorial := by ring

omit [LinearOrder V] in
include hC0 hφ0 hφθ hφm in
/-- **The corrected matrix of a finite iterate is nonnegative.** -/
theorem cutoffCorrection_residual_nonneg (hθf : 0 ≤ θ * f) (k : ℕ) (x y : V) :
    0 ≤ (C - cutoffCorrectionIter φ C k + cutoffCorrectionIter φ C k * C) x y := by
  cases k with
  | zero => simpa [cutoffCorrectionIter] using hC0 x y
  | succ k =>
    have hF0 := cutoffCorrectionIter_nonneg (C := C) hφ0 k
    have hstep : cutoffCorrectionIter φ C (k + 1) x y =
        φ y ((C + cutoffCorrectionIter φ C k * C) x y) := by
      rw [cutoffCorrectionIter_succ]; rfl
    have hcut := cutoff_le_self hφθ hθf y (correctionInput_nonneg hC0 hF0 x y)
    have hgrow : (cutoffCorrectionIter φ C k * C) x y ≤
        (cutoffCorrectionIter φ C (k + 1) * C) x y :=
      Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_right
        (cutoffCorrectionIter_le_succ hC0 hφ0 hφm k x z) (hC0 z y)
    rw [← hstep, Matrix.add_apply] at hcut
    rw [Matrix.add_apply, Matrix.sub_apply]
    linarith

include hC hC0 hCf hC1 hφ0 hφθ hφm hφL in
/-- **Fully corrected columns have small residuals.** If the cutoff of column `y` leaves at most
`θ₂ f` behind, the corrected matrix of the `k`-th iterate has entries at most
`θ₂ f + f e^(1 / θ) (L / θ)^k / k!` in that column [OpenAI2026LogSpace, Lemma 4.4]. -/
theorem cutoffCorrection_residual_le (hf : 0 < f) (hθ : 0 < θ) (hL : 0 ≤ L) {θ₂ : ℝ} {y : V}
    (hgood : ∀ t, t - θ₂ * f ≤ φ y t) (k : ℕ) (x : V) :
    (C - cutoffCorrectionIter φ C k + cutoffCorrectionIter φ C k * C) x y ≤
      θ₂ * f + f * Real.exp (1 / θ) * (L / θ) ^ k / k.factorial := by
  set E := cutoffCorrectionFix φ C
  set F := cutoffCorrectionIter φ C k
  have hEfix : E x y = φ y ((C + E * C) x y) := fix_apply hC x y
  have hΔ := cutoffCorrectionFix_sub_iter_le hC hC0 hCf hC1 hφ0 hφθ hφm hφL hf hθ hL k x y
  have hΔC : (F * C) x y ≤ (E * C) x y :=
    Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_right
      (cutoffCorrectionIter_le_fix hC hC0 hφ0 hφm k x z) (hC0 z y)
  have hT := hgood ((C + E * C) x y)
  rw [← hEfix] at hT
  simp only [Matrix.add_apply, Matrix.sub_apply] at hT hΔC ⊢
  linarith

/-- **A constant number of iterations suffices**: for every accuracy `δ > 0` there is `k`, depending
only on `θ`, `L` and `δ`, with `e^(1 / θ) (L / θ)^k / k! ≤ δ` [OpenAI2026LogSpace, Lemma 4.1]. -/
theorem exists_factorial_bound_le (θ L : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ k : ℕ, Real.exp (1 / θ) * (L / θ) ^ k / k.factorial ≤ δ := by
  have h := (FloorSemiring.tendsto_pow_div_factorial_atTop (L / θ)).const_mul
    (Real.exp (1 / θ))
  rw [mul_zero] at h
  obtain ⟨k, hk⟩ := (h.eventually (gt_mem_nhds hδ)).exists
  exact ⟨k, by rw [mul_div_assoc]; exact hk.le⟩

end Bounds

end Matrix
