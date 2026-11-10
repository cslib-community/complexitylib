/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, beside `Mathlib/LinearAlgebra/Matrix/Farkas.lean`)

public import CslibFrontier.Foundations.LinearAlgebra.Matrix.Farkas
public import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Basic solutions and small integer solutions of linear systems

A nonnegative solution of `A *ᵥ x = b` over a linearly ordered field can be moved along kernel
directions until no nonzero kernel vector of `A` is supported inside its support: it becomes a
*basic* solution. For an integer matrix this pins the solution down as the unique solution of the
Gram system of its support columns, so Cramer's rule writes it as `p / d` with integers `p` and
`d` that are determinants of integer matrices; Mathlib's `Matrix.det_le` bounds them. The usual
reduction of `A *ᵥ x ≤ b` to equality form with nonnegative variables, and of a Farkas certificate
(`Matrix.not_exists_mulVec_le_iff`) to a nonnegative solution of `[Aᵀ; bᵀ] y = (0, -1)`, give
bounds of the same form for inequality systems and for certificates of infeasibility. These are
the size bounds behind the membership of rational linear-programming feasibility in `NP ∩ coNP`
(`Cslib.Complexity.LPFeasibility.mem_NP`, `Cslib.Complexity.LPFeasibility.mem_coNP`).

`Matrix.det_le` is the bound `|det M| ≤ (card n)! * c ^ card n` from the Leibniz expansion rather
than Hadamard's inequality. It is weaker by a factor of at most `(card n)!`, still polynomial in
bit length, which is all the complexity bounds need.

## Main results

* `Matrix.exists_nonneg_mulVec_eq_forall_mulVec_eq_zero`: existence of basic solutions.
* `Matrix.exists_int_nonneg_mulVec_eq`: an integer system `A *ᵥ x = b` with a nonnegative
  solution has one of the form `p / d` with `0 ≤ p`, `0 < d` and
  `p j, d ≤ (card n)! * (card m * B ^ 2 + 1) ^ card n`, `B` bounding the entries.
* `Matrix.exists_int_mulVec_le`: for `A *ᵥ x ≤ b`, a solution `p / d` with `|p j|` and `0 < d`
  at most `(2 * card n + card m)! * (card m * (B + 1) ^ 2 + 1) ^ (2 * card n + card m)`.
* `Matrix.exists_int_farkas_certificate`: an infeasible integer system `A *ᵥ x ≤ b` has an integer
  Farkas certificate `y ≥ 0`, `y ᵥ* A = 0`, `y ⬝ᵥ b < 0` with
  `y i ≤ (card m)! * ((card n + 1) * (B + 1) ^ 2 + 1) ^ card m`.

## References

* [Schrijver1986], Sections 3.2 and 10.1
-/

public section

open Finset
open scoped Nat

namespace Matrix

variable {m n K : Type*} [Fintype m] [Fintype n]
  [Field K] [LinearOrder K] [IsStrictOrderedRing K]

omit [Fintype m] in
/-- **Basic solutions.** A nonnegative solution of `A *ᵥ x = b` can be replaced by one whose
support lies in that of `x` and carries no nonzero kernel vector of `A`, so the columns of `A` on
its support are linearly independent. -/
theorem exists_nonneg_mulVec_eq_forall_mulVec_eq_zero {A : Matrix m n K} {b : m → K} {x : n → K}
    (hx : 0 ≤ x) (hAx : A *ᵥ x = b) :
    ∃ y, 0 ≤ y ∧ A *ᵥ y = b ∧ (∀ j, x j = 0 → y j = 0) ∧
      ∀ w : n → K, (∀ j, y j = 0 → w j = 0) → A *ᵥ w = 0 → w = 0 := by
  classical
  suffices h : ∀ k (x : n → K), #{j | x j ≠ 0} = k → 0 ≤ x → A *ᵥ x = b →
      ∃ y, 0 ≤ y ∧ A *ᵥ y = b ∧ (∀ j, x j = 0 → y j = 0) ∧
        ∀ w : n → K, (∀ j, y j = 0 → w j = 0) → A *ᵥ w = 0 → w = 0 from h _ x rfl hx hAx
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro x hk hx hAx
  by_cases hmin : ∀ w : n → K, (∀ j, x j = 0 → w j = 0) → A *ᵥ w = 0 → w = 0
  · exact ⟨x, hx, hAx, fun _ h => h, hmin⟩
  push Not at hmin
  obtain ⟨w₀, hw₀s, hw₀A, hw₀⟩ := hmin
  obtain ⟨j₀, hj₀⟩ := Function.ne_iff.1 hw₀
  obtain ⟨w, hws, hwA, j₀, hwj₀⟩ : ∃ w : n → K, (∀ j, x j = 0 → w j = 0) ∧ A *ᵥ w = 0 ∧
      ∃ j₀, 0 < w j₀ := by
    rcases lt_or_gt_of_ne hj₀ with h | h
    · refine ⟨-w₀, fun j hj => by simp [hw₀s j hj], by simp [mulVec_neg, hw₀A], j₀, ?_⟩
      simpa using h
    · exact ⟨w₀, hw₀s, hw₀A, j₀, h⟩
  have hs : ({j | 0 < w j} : Finset n).Nonempty := ⟨j₀, by simp [hwj₀]⟩
  obtain ⟨j₁, hj₁s, hj₁⟩ := Finset.exists_min_image _ (fun j => x j / w j) hs
  have hwj₁ : 0 < w j₁ := by simpa using hj₁s
  set t := x j₁ / w j₁ with ht_def
  have ht : 0 ≤ t := div_nonneg (hx j₁) hwj₁.le
  set x' := x - t • w with hx'_def
  have hx' : 0 ≤ x' := by
    intro j
    simp only [x', Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, sub_nonneg]
    rcases le_or_gt (w j) 0 with h | h
    · exact (mul_nonpos_of_nonneg_of_nonpos ht h).trans (hx j)
    · have := hj₁ j (by simp [h])
      rwa [le_div_iff₀ h] at this
  have hAx' : A *ᵥ x' = b := by
    simp [x', mulVec_sub, mulVec_smul, hwA, hAx]
  have hsub : ∀ j, x j = 0 → x' j = 0 := fun j hj => by
    simp [x', hj, hws j hj]
  have hx'j₁ : x' j₁ = 0 := by
    simp only [x', Pi.sub_apply, Pi.smul_apply, smul_eq_mul, t]
    rw [div_mul_cancel₀ _ hwj₁.ne', sub_self]
  have hxj₁ : x j₁ ≠ 0 := fun h => hwj₁.ne' (hws j₁ h)
  have hlt : #{j | x' j ≠ 0} < k := by
    rw [← hk]
    apply Finset.card_lt_card
    refine ⟨fun j => ?_, fun h => ?_⟩
    · simp only [mem_filter, mem_univ, true_and]
      exact mt (hsub j)
    · have := h (show j₁ ∈ ({j | x j ≠ 0} : Finset n) by simp [hxj₁])
      simp [hx'j₁] at this
  obtain ⟨y, hy, hAy, hxy, hymin⟩ := ih _ hlt x' rfl hx' hAx'
  exact ⟨y, hy, hAy, fun j hj => hxy j (hsub j hj), hymin⟩

/-- A sum of `card m` products of entries bounded by `B` is bounded by `card m * B ^ 2`. -/
private theorem abs_sum_mul_le {u v : m → ℤ} {B : ℕ} (hu : ∀ i, |u i| ≤ B) (hv : ∀ i, |v i| ≤ B) :
    |∑ i, u i * v i| ≤ (Fintype.card m * B ^ 2 : ℕ) := by
  calc |∑ i, u i * v i| ≤ ∑ i, |u i * v i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : m, ((B : ℤ) * B) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul]
        exact mul_le_mul (hu i) (hv i) (abs_nonneg _) (Nat.cast_nonneg _)
    _ = (Fintype.card m * B ^ 2 : ℕ) := by
        simp [Finset.sum_const, Finset.card_univ, sq]

/-- `|det M| ≤ (card n)! * C ^ card n` for an integer matrix with entries of absolute value at
most `C` (`Matrix.det_le` with the usual absolute value). -/
private theorem abs_det_le [DecidableEq n] {M : Matrix n n ℤ} {C : ℕ}
    (hM : ∀ j k, |M j k| ≤ C) : |M.det| ≤ ((Fintype.card n)! * C ^ Fintype.card n : ℕ) := by
  simpa using det_le (abv := AbsoluteValue.abs) hM

/-- **The Gram system of a basic solution.** If `A *ᵥ y = b` and no nonzero kernel vector of `A`
is supported inside the support of `y`, then `y` is the unique solution of a square integer
system `G *ᵥ y = c`: the Gram system `Aᵀ A` restricted to the support of `y`, padded by the
identity outside it. Its entries are at most `card m * B ^ 2 + 1` when those of `A` and `b` are
at most `B`. -/
private theorem exists_gram_system [DecidableEq n] {A : Matrix m n ℤ} {b : m → ℤ} {B : ℕ}
    (hA : ∀ i j, |A i j| ≤ B) (hb : ∀ i, |b i| ≤ B) {y : n → K}
    (hAy : A.map (Int.cast : ℤ → K) *ᵥ y = fun i => (b i : K))
    (hymin : ∀ w : n → K, (∀ j, y j = 0 → w j = 0) → A.map (Int.cast : ℤ → K) *ᵥ w = 0 → w = 0) :
    ∃ (G : Matrix n n ℤ) (c : n → ℤ), G.map (Int.cast : ℤ → K) *ᵥ y = (fun j => (c j : K)) ∧
      G.det ≠ 0 ∧ (∀ j, |c j| ≤ (Fintype.card m * B ^ 2 + 1 : ℕ)) ∧
      ∀ j k, |G j k| ≤ (Fintype.card m * B ^ 2 + 1 : ℕ) := by
  classical
  set AK : Matrix m n K := A.map (Int.cast : ℤ → K) with hAK
  let G : Matrix n n ℤ := of fun j k =>
    if y j ≠ 0 ∧ y k ≠ 0 then ∑ i, A i j * A i k else if j = k then 1 else 0
  let c : n → ℤ := fun j => if y j ≠ 0 then ∑ i, A i j * b i else 0
  set GK : Matrix n n K := G.map (Int.cast : ℤ → K) with hGK
  have hGK_apply : ∀ j k, GK j k =
      if y j ≠ 0 ∧ y k ≠ 0 then ((AKᵀ * AK) j k) else if j = k then 1 else 0 := by
    intro j k
    rw [hGK, hAK, map_apply]
    simp only [G, of_apply]
    split_ifs <;> push_cast <;> rfl
  -- Off the support `G` acts as the identity; on it, as `Aᵀ A` on vectors supported there.
  have hG0 : ∀ (v : n → K) j, y j = 0 → (GK *ᵥ v) j = v j := by
    intro v j hj
    simp only [mulVec, dotProduct, hGK_apply]
    simp [hj]
  have hG1 : ∀ v : n → K, (∀ k, y k = 0 → v k = 0) → ∀ j, y j ≠ 0 →
      (GK *ᵥ v) j = ((AKᵀ * AK) *ᵥ v) j := by
    intro v hv j hj
    simp only [mulVec, dotProduct]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : y k = 0
    · simp [hv k hk]
    · rw [hGK_apply, ite_eq_left ⟨hj, hk⟩]
  have hGy : GK *ᵥ y = fun j => (c j : K) := by
    funext j
    by_cases hj : y j = 0
    · rw [hG0 y j hj]
      simp [c, hj]
    · rw [hG1 y (fun _ h => h) j hj, ← mulVec_mulVec, hAy]
      simp [c, hj, mulVec, dotProduct, AK]
  -- `G` is nonsingular: a kernel vector `v` is supported in that of `y` and `‖A v‖² = 0`.
  have hinj : ∀ v : n → K, GK *ᵥ v = 0 → v = 0 := by
    intro v hv
    have hv0 : ∀ k, y k = 0 → v k = 0 := fun k hk => by
      simpa [hG0 v k hk] using congrFun hv k
    have hv1 : ∀ j, y j ≠ 0 → (AKᵀ *ᵥ (AK *ᵥ v)) j = 0 := fun j hj => by
      simpa [mulVec_mulVec, hG1 v hv0 j hj] using congrFun hv j
    have hAv : AK *ᵥ v = 0 := by
      rw [← dotProduct_self_eq_zero]
      conv_lhs => rw [dotProduct_mulVec, ← mulVec_transpose]
      refine Finset.sum_eq_zero fun j _ => ?_
      by_cases hj : y j = 0
      · simp [hv0 j hj]
      · simp [hv1 j hj]
    exact hymin v hv0 hAv
  have hdet : G.det ≠ 0 := fun h => by
    have hGK0 : GK.det = 0 := by
      have hcast : ((G.det : ℤ) : K) = GK.det := (Int.castRingHom K).map_det G
      rw [← hcast, h, Int.cast_zero]
    obtain ⟨v, hv, hGv⟩ := exists_mulVec_eq_zero_iff.2 hGK0
    exact hv (hinj v hGv)
  refine ⟨G, c, hGy, hdet, fun j => ?_, fun j k => ?_⟩
  · simp only [c]
    split_ifs
    · exact (abs_sum_mul_le (fun k => hA k j) hb).trans (by push_cast; linarith)
    · rw [abs_zero]
      positivity
  · simp only [G, of_apply]
    split_ifs
    · exact (abs_sum_mul_le (fun i => hA i j) (fun i => hA i k)).trans (by push_cast; linarith)
    · rw [abs_one]
      exact_mod_cast Nat.le_add_left 1 _
    · rw [abs_zero]
      positivity

omit [Fintype m] in
/-- **Cramer's rule over an extension.** If the integer system `G *ᵥ y = c` holds after casting
into a commutative ring `R`, then the cast of Cramer's integer vector `cramer G c` is
`det G • y`. -/
private theorem intCast_cramer_eq_det_smul {R : Type*} [CommRing R] [DecidableEq n]
    {G : Matrix n n ℤ} {c : n → ℤ} {y : n → R}
    (hGy : G.map (Int.cast : ℤ → R) *ᵥ y = fun j => (c j : R)) :
    (fun j => (cramer G c j : R)) = (G.det : R) • y := by
  have h := (Int.castRingHom R).map_mulVec (adjugate G) c
  simp only [eq_intCast, Int.coe_castRingHom] at h
  calc (fun j => (cramer G c j : R))
      = (adjugate G).map (Int.cast : ℤ → R) *ᵥ fun j => (c j : R) := by
        rw [cramer_eq_adjugate_mulVec]
        exact funext h
    _ = (G.det : R) • y := by
        have hadj : (adjugate G).map (Int.cast : ℤ → R) = adjugate (G.map Int.cast) :=
          (Int.castRingHom R).map_adjugate G
        have hdet : ((G.det : ℤ) : R) = (G.map (Int.cast : ℤ → R)).det :=
          (Int.castRingHom R).map_det G
        rw [← hGy, mulVec_mulVec, hadj, adjugate_mul, smul_mulVec, one_mulVec, hdet]

/-- **Small basic solutions.** If an integer system `A *ᵥ x = b` with entries of absolute value at
most `B` has a nonnegative solution over some linearly ordered field, then it has a nonnegative
rational solution `p / d` with `p` and `d` integers bounded by
`(card n)! * (card m * B ^ 2 + 1) ^ card n`. -/
theorem exists_int_nonneg_mulVec_eq {A : Matrix m n ℤ} {b : m → ℤ} {B : ℕ}
    (hA : ∀ i j, |A i j| ≤ B) (hb : ∀ i, |b i| ≤ B)
    {x : n → K} (hx : 0 ≤ x) (hAx : A.map (Int.cast : ℤ → K) *ᵥ x = fun i => (b i : K)) :
    ∃ (d : ℤ) (p : n → ℤ), 0 < d ∧ 0 ≤ p ∧ A *ᵥ p = d • b ∧
      d ≤ ((Fintype.card n)! * (Fintype.card m * B ^ 2 + 1) ^ Fintype.card n : ℕ) ∧
      ∀ j, p j ≤ ((Fintype.card n)! * (Fintype.card m * B ^ 2 + 1) ^ Fintype.card n : ℕ) := by
  classical
  set N : ℕ := (Fintype.card n)! * (Fintype.card m * B ^ 2 + 1) ^ Fintype.card n
  -- Pass to a basic solution `y`, the unique solution of a square integer system `G y = c`;
  -- Cramer's rule writes `det G • y` as the integer vector `cramer G c`.
  obtain ⟨y, hy, hAy, -, hymin⟩ := exists_nonneg_mulVec_eq_forall_mulVec_eq_zero hx hAx
  obtain ⟨G, c, hGy, hd0, hc, hG⟩ := exists_gram_system hA hb hAy hymin
  -- Both `det G` and the entries of `cramer G c` are determinants of matrices with small entries.
  have hdbound : |G.det| ≤ N := abs_det_le hG
  have hpbound : ∀ j, |cramer G c j| ≤ N := fun j => by
    rw [cramer_apply]
    refine abs_det_le fun k l => ?_
    rw [updateCol_apply]
    split_ifs
    · exact hc k
    · exact hG k l
  -- Normalize the sign: `d = |det G|` and `p = ±cramer G c` still satisfy `p = d • y` in `K`.
  obtain ⟨d, p, hd, hpy, hdN, hpN⟩ : ∃ (d : ℤ) (p : n → ℤ), 0 < d ∧
      (fun j => (p j : K)) = (d : K) • y ∧ d ≤ N ∧ ∀ j, |p j| ≤ N := by
    have hp := intCast_cramer_eq_det_smul hGy
    rcases lt_or_gt_of_ne hd0 with hneg | hpos
    · refine ⟨-G.det, -cramer G c, neg_pos.2 hneg, ?_, by rwa [← abs_of_neg hneg],
        fun j => by simpa using hpbound j⟩
      simp only [Pi.neg_apply, Int.cast_neg, neg_smul, ← hp]
      rfl
    · exact ⟨G.det, cramer G c, hpos, hp, (le_abs_self _).trans hdbound, hpbound⟩
  refine ⟨d, p, hd, fun j => ?_, ?_, hdN, fun j => (le_abs_self _).trans (hpN j)⟩
  · have h : (0 : K) ≤ p j := by
      rw [congrFun hpy j]
      exact mul_nonneg (by exact_mod_cast hd.le) (hy j)
    exact_mod_cast h
  · funext i
    apply Int.cast_injective (α := K)
    have h1 := (Int.castRingHom K).map_mulVec A p i
    simp only [eq_intCast] at h1
    rw [h1]
    change (A.map (Int.cast : ℤ → K) *ᵥ fun j => (p j : K)) i = _
    rw [hpy, mulVec_smul, hAy]
    simp

/-- **Small solutions of integer inequality systems.** If `A *ᵥ x ≤ b`, with integer entries of
absolute value at most `B`, has a solution over some linearly ordered field, then it has a
rational solution `p / d` with `p` and `d` integers of absolute value at most
`(2 * card n + card m)! * (card m * (B + 1) ^ 2 + 1) ^ (2 * card n + card m)`. -/
theorem exists_int_mulVec_le {A : Matrix m n ℤ} {b : m → ℤ} {B : ℕ}
    (hA : ∀ i j, |A i j| ≤ B) (hb : ∀ i, |b i| ≤ B)
    {x : n → K} (hAx : A.map (Int.cast : ℤ → K) *ᵥ x ≤ fun i => (b i : K)) :
    ∃ (d : ℤ) (p : n → ℤ), 0 < d ∧ A *ᵥ p ≤ d • b ∧
      d ≤ ((2 * Fintype.card n + Fintype.card m)! *
        (Fintype.card m * (B + 1) ^ 2 + 1) ^ (2 * Fintype.card n + Fintype.card m) : ℕ) ∧
      ∀ j, |p j| ≤ ((2 * Fintype.card n + Fintype.card m)! *
        (Fintype.card m * (B + 1) ^ 2 + 1) ^ (2 * Fintype.card n + Fintype.card m) : ℕ) := by
  classical
  set AK : Matrix m n K := A.map (Int.cast : ℤ → K) with hAK
  let A' : Matrix m (n ⊕ n ⊕ m) ℤ := of fun i =>
    Sum.elim (fun j => A i j) (Sum.elim (fun j => -A i j) fun i' => if i = i' then 1 else 0)
  have hA' : ∀ i j, |A' i j| ≤ (B + 1 : ℕ) := by
    intro i j
    rcases j with j | j | i'
    · simp only [A', of_apply, Sum.elim_inl]
      exact (hA i j).trans (by push_cast; linarith)
    · simp only [A', of_apply, Sum.elim_inl, Sum.elim_inr, abs_neg]
      exact (hA i j).trans (by push_cast; linarith)
    · simp only [A', of_apply, Sum.elim_inr]
      split_ifs
      · simp
      · rw [abs_zero]
        positivity
  have hb' : ∀ i, |b i| ≤ (B + 1 : ℕ) := fun i => (hb i).trans (by simp)
  let z : n ⊕ n ⊕ m → K :=
    Sum.elim (fun j => max (x j) 0) (Sum.elim (fun j => max (-x j) 0)
      fun i => (b i : K) - (AK *ᵥ x) i)
  have hz : 0 ≤ z := by
    intro j
    rcases j with j | j | i
    · exact le_max_right _ _
    · exact le_max_right _ _
    · exact sub_nonneg.2 (hAx i)
  have hAz : A'.map (Int.cast : ℤ → K) *ᵥ z = fun i => (b i : K) := by
    funext i
    simp only [mulVec, dotProduct, Fintype.sum_sum_type, map_apply, A', of_apply, Sum.elim_inl,
      Sum.elim_inr, z]
    have hx : ∀ j, max (x j) 0 - max (-x j) 0 = x j := fun j =>
      max_zero_sub_max_neg_zero_eq_self (x j)
    simp only [Int.cast_neg, neg_mul, Finset.sum_neg_distrib, Int.cast_ite, Int.cast_one,
      Int.cast_zero, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    have : ∑ j, (A i j : K) * max (x j) 0 + -∑ j, (A i j : K) * max (-x j) 0 =
        ∑ j, AK i j * x j := by
      rw [← sub_eq_add_neg, ← Finset.sum_sub_distrib]
      simp only [← mul_sub, hx, AK, map_apply]
    linarith
  obtain ⟨d, p', hd, hp', hAp', hdN, hpN⟩ := exists_int_nonneg_mulVec_eq hA' hb' hz hAz
  have hcard : Fintype.card (n ⊕ n ⊕ m) = 2 * Fintype.card n + Fintype.card m := by
    simp only [Fintype.card_sum]
    ring
  rw [hcard] at hdN hpN
  refine ⟨d, fun j => p' (Sum.inl j) - p' (Sum.inr (Sum.inl j)), hd, fun i => ?_, hdN, fun j => ?_⟩
  · have h := congrFun hAp' i
    simp only [mulVec, dotProduct, Fintype.sum_sum_type, A', of_apply, Sum.elim_inl,
      Sum.elim_inr, Pi.smul_apply, smul_eq_mul, neg_mul, Finset.sum_neg_distrib, ite_mul, one_mul,
      zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true] at h
    simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib]
    have := hp' (Sum.inr (Sum.inr i))
    simp only [Pi.zero_apply] at this
    linarith
  · have h1 := hp' (Sum.inl j)
    have h2 := hp' (Sum.inr (Sum.inl j))
    have h3 := hpN (Sum.inl j)
    have h4 := hpN (Sum.inr (Sum.inl j))
    simp only [Pi.zero_apply] at h1 h2
    rw [abs_sub_le_iff]
    constructor <;> linarith

/-- **Small Farkas certificates.** If `A *ᵥ x ≤ b`, with integer entries of absolute value at most
`B`, has no solution over a linearly ordered field, then an integer vector `y ≥ 0` with
`y ᵥ* A = 0` and `y ⬝ᵥ b < 0` certifies it, with entries at most
`(card m)! * ((card n + 1) * (B + 1) ^ 2 + 1) ^ card m`. -/
theorem exists_int_farkas_certificate {A : Matrix m n ℤ} {b : m → ℤ} {B : ℕ}
    (hA : ∀ i j, |A i j| ≤ B) (hb : ∀ i, |b i| ≤ B)
    (h : ¬∃ x : n → K, A.map (Int.cast : ℤ → K) *ᵥ x ≤ fun i => (b i : K)) :
    ∃ y : m → ℤ, 0 ≤ y ∧ y ᵥ* A = 0 ∧ y ⬝ᵥ b < 0 ∧
      ∀ i, y i ≤
        ((Fintype.card m)! * ((Fintype.card n + 1) * (B + 1) ^ 2 + 1) ^ Fintype.card m : ℕ) := by
  classical
  obtain ⟨y, hy, hyA, hyb⟩ := (not_exists_mulVec_le_iff _ _).1 h
  -- The system `[Aᵀ; bᵀ] y = (0, -1)`, `y ≥ 0`.
  let M : Matrix (n ⊕ Unit) m ℤ := of fun r i => Sum.elim (fun j => A i j) (fun _ => b i) r
  let e : n ⊕ Unit → ℤ := Sum.elim 0 fun _ => -1
  have hM : ∀ r i, |M r i| ≤ (B + 1 : ℕ) := by
    intro r i
    rcases r with j | u
    · exact (hA i j).trans (by push_cast; linarith)
    · exact (hb i).trans (by push_cast; linarith)
  have he : ∀ r, |e r| ≤ (B + 1 : ℕ) := by
    intro r
    rcases r with j | u
    · simp only [e, Sum.elim_inl, Pi.zero_apply, abs_zero]
      positivity
    · simp [e]
  set s : K := y ⬝ᵥ (fun i => (b i : K)) with hs
  have hy' : 0 ≤ (-s⁻¹) • y := smul_nonneg (neg_nonneg.2 (inv_nonpos.2 hyb.le)) hy
  have hMy : M.map (Int.cast : ℤ → K) *ᵥ ((-s⁻¹) • y) = fun r => (e r : K) := by
    funext r
    rcases r with j | u
    · have h1 := congrFun hyA j
      simp only [vecMul, dotProduct, map_apply, Pi.zero_apply] at h1
      simp only [mulVec, dotProduct, map_apply, M, e, of_apply, Sum.elim_inl, Pi.smul_apply,
        smul_eq_mul, Pi.zero_apply, Int.cast_zero]
      calc ∑ i, (A i j : K) * (-s⁻¹ * y i) = -s⁻¹ * ∑ i, y i * (A i j : K) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => by ring
        _ = 0 := by rw [h1, mul_zero]
    · simp only [mulVec, dotProduct, map_apply, M, e, of_apply, Sum.elim_inr, Pi.smul_apply,
        smul_eq_mul, Int.cast_neg, Int.cast_one]
      calc ∑ i, (b i : K) * (-s⁻¹ * y i) = -s⁻¹ * s := by
            rw [hs, dotProduct, Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => by ring
        _ = -1 := by rw [neg_mul, inv_mul_cancel₀ hyb.ne]
  obtain ⟨d, q, hd, hq, hMq, -, hqN⟩ := exists_int_nonneg_mulVec_eq hM he hy' hMy
  have hcard : Fintype.card (n ⊕ Unit) = Fintype.card n + 1 := by simp
  rw [hcard] at hqN
  refine ⟨q, hq, ?_, ?_, hqN⟩
  · funext j
    have h1 := congrFun hMq (Sum.inl j)
    simp only [mulVec, dotProduct, M, e, of_apply, Sum.elim_inl, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply, mul_zero] at h1
    simp only [vecMul, dotProduct, Pi.zero_apply]
    rw [← h1]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  · have h1 := congrFun hMq (Sum.inr ())
    simp only [mulVec, dotProduct, M, e, of_apply, Sum.elim_inr, Pi.smul_apply, smul_eq_mul,
      mul_neg, mul_one] at h1
    have h2 : ∑ i, q i * b i = -d := by
      rw [← h1]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    simp only [dotProduct]
    linarith

end Matrix
