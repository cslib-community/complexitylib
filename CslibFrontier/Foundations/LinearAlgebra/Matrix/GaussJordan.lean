/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, beside `LinearAlgebra/Matrix/Echelon`)

public import CslibFrontier.Init
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Staged Gauss–Jordan elimination and matrix rank

This file computes the rank of a matrix over a field by Gauss–Jordan elimination without row
swaps, one stage per column. Stage `j` looks for the first row that is zero on the columns before
`j` and nonzero at `j` (`Matrix.GaussJordan.pivotRow`). If there is one, it subtracts multiples of
that row from every other row to clear column `j` (`Matrix.GaussJordan.stage`); otherwise it leaves
the matrix unchanged. Rows are never swapped, so every stage is a fixed function of the matrix.

Each stage multiplies on the left by an invertible matrix, so it preserves the rank. After all `c`
stages, every nonzero row owns at least one column where it is nonzero and every other row is zero
(`Matrix.GaussJordan.exists_pivot_of_reduce_ne_zero`); distinct rows own distinct columns, since an
owned column has only one nonzero entry. The rank is therefore the number of nonzero rows
(`Matrix.GaussJordan.rank_eq_card_reduce_ne_zero`). A row may own several columns: `!![1, 1]` is
already reduced and has rank `1`. The rows of the output are not sorted into row echelon form, so
`Matrix.IsPivotedBy` does not apply directly.

Over `ZMod 2` a stage needs no division: the pivot entry is `1`, and the stage adds the pivot row
to every other row with a `1` in column `j` (`Matrix.GaussJordan.stage_apply_zmod_two`). Each entry
of a stage is then an XOR of ANDs of entries and pivot indicators, and the pivot is a prefix
condition on column `j` (`Matrix.GaussJordan.pivotRow_eq_some_iff`). A Boolean circuit with
unbounded fan-in AND and OR gates can evaluate one stage in constant depth; the full reduction
chains `c` stages, so it has polynomial size and depth `O(c)`.

## Main definitions

* `Matrix.GaussJordan.IsFreeBefore A k i`: row `i` is zero on the columns before `k`.
* `Matrix.GaussJordan.eliminate A j p`: clear column `j` with pivot row `p`.
* `Matrix.GaussJordan.pivotRow A j`: the first row that is zero before column `j` and nonzero at
  `j`, if any (the minimum of `Matrix.GaussJordan.pivotCandidates A j`).
* `Matrix.GaussJordan.stage A j`: one elimination stage at column `j`.
* `Matrix.GaussJordan.reduce A`: the stages for columns `0, …, c - 1`, in order.

## Main results

* `Matrix.GaussJordan.rank_stage`, `Matrix.GaussJordan.rank_reduce`: the stages preserve rank.
* `Matrix.GaussJordan.exists_pivot_of_reduce_ne_zero`: every nonzero row of `reduce A` owns a
  column where every other row is zero.
* `Matrix.GaussJordan.rank_eq_card_reduce_ne_zero`: the rank of `A` is the number of nonzero rows
  of `reduce A`.
* `Matrix.GaussJordan.pivotRow_eq_some_iff`, `Matrix.GaussJordan.pivotRow_eq_none_iff`: the pivot
  row as a prefix condition.
* `Matrix.GaussJordan.stage_apply_zmod_two`: the division-free form of a stage over `ZMod 2`.

## References

Gauss–Jordan elimination is standard. Computing a GF(2) rank this way is the constructivity step of
the rank property in [Razborov and Rudich, §3.2][RazborovRudich1997].
-/

public section

namespace Matrix.GaussJordan

open Finset

variable {m : Type*} {c : ℕ} {K : Type*}

section Invariant

variable [Zero K]

/-- Row `i` of `A` is zero on the columns before `k`. -/
@[expose] def IsFreeBefore (A : Matrix m (Fin c) K) (k : ℕ) (i : m) : Prop :=
  ∀ l : Fin c, l.1 < k → A i l = 0

instance [DecidableEq K] (A : Matrix m (Fin c) K) (k : ℕ) : DecidablePred (IsFreeBefore A k) :=
  -- unfolded explicitly: instance search does not see through a `Matrix` under a binder
  fun i => inferInstanceAs (Decidable (∀ l : Fin c, l.1 < k → A i l = 0))

/-- The invariant after the stages for the columns before `k`: every row is either free before `k`
or owns a column before `k`, where it is nonzero and every other row is zero. -/
private def IsReducedBefore (B : Matrix m (Fin c) K) (k : ℕ) : Prop :=
  ∀ i, IsFreeBefore B k i ∨ ∃ l : Fin c, l.1 < k ∧ B i l ≠ 0 ∧ ∀ i', i' ≠ i → B i' l = 0

private theorem isReducedBefore_zero (B : Matrix m (Fin c) K) : IsReducedBefore B 0 :=
  fun _ => Or.inl fun _ hl => absurd hl (Nat.not_lt_zero _)

/-- Once every column is processed, a nonzero row owns a column where every other row is zero. -/
private theorem exists_pivot_of_isReducedBefore {B : Matrix m (Fin c) K}
    (hB : IsReducedBefore B c) {i : m} (hi : B i ≠ 0) :
    ∃ l, B i l ≠ 0 ∧ ∀ i', i' ≠ i → B i' l = 0 := by
  rcases hB i with hfree | ⟨l, -, hne, hcol⟩
  · exact (hi (funext fun l => hfree l l.2)).elim
  · exact ⟨l, hne, hcol⟩

end Invariant

/-! ### Elimination with a fixed pivot row -/

section Eliminate

variable [DecidableEq m] [Field K]

/-- Clear column `j` using pivot row `p`: every row `i ≠ p` loses `A i j / A p j` times row `p`. -/
@[expose] def eliminate (A : Matrix m (Fin c) K) (j : Fin c) (p : m) : Matrix m (Fin c) K :=
  of fun i l => if i = p then A i l else A i l - A i j / A p j * A p l

theorem eliminate_apply_self (A : Matrix m (Fin c) K) (j : Fin c) (p : m) (l : Fin c) :
    eliminate A j p p l = A p l := by
  simp [eliminate]

theorem eliminate_apply_of_ne {A : Matrix m (Fin c) K} {j : Fin c} {p i : m} (h : i ≠ p)
    (l : Fin c) : eliminate A j p i l = A i l - A i j / A p j * A p l := by
  simp [eliminate, h]

/-- Elimination with a pivot row that is zero in column `l` leaves column `l` unchanged. -/
theorem eliminate_apply_of_eq_zero {A : Matrix m (Fin c) K} {j l : Fin c} {p : m}
    (h : A p l = 0) (i : m) : eliminate A j p i l = A i l := by
  by_cases hi : i = p
  · rw [hi, eliminate_apply_self]
  · rw [eliminate_apply_of_ne hi, h, mul_zero, sub_zero]

/-- Elimination with a pivot nonzero in column `j` clears column `j` outside the pivot row. -/
theorem eliminate_apply_of_ne_of_ne_zero {A : Matrix m (Fin c) K} {j : Fin c} {p i : m}
    (hp : A p j ≠ 0) (h : i ≠ p) : eliminate A j p i j = 0 := by
  rw [eliminate_apply_of_ne h, div_mul_cancel₀ _ hp, sub_self]

/-- Elimination preserves the rank. It is left multiplication by `1 - D`, where `D` is supported
on column `p` off row `p`; then `D * D = 0`, so `1 + D` inverts `1 - D`. -/
theorem rank_eliminate [Finite m] (A : Matrix m (Fin c) K) (j : Fin c) (p : m) :
    (eliminate A j p).rank = A.rank := by
  have := Fintype.ofFinite m
  let D : Matrix m m K := of fun i q => if q = p ∧ i ≠ p then A i j / A p j else 0
  have hD : D * D = 0 := by
    ext i k
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine sum_eq_zero fun q _ => ?_
    by_cases hq : q = p <;> simp [D, hq]
  have hinv : (1 + D) * (1 - D) = 1 := by
    rw [add_mul, one_mul, mul_sub, mul_one, hD, sub_zero, sub_add_cancel]
  have hA : eliminate A j p = (1 - D) * A := by
    ext i l
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, Matrix.mul_apply,
      sum_eq_single p (fun q _ hq => by simp [D, hq]) (by simp)]
    by_cases hi : i = p
    · simp [D, hi, eliminate_apply_self]
    · simp [D, hi, eliminate_apply_of_ne hi]
  rw [hA, rank_mul_eq_right_of_isUnit_det _ _ (isUnit_det_of_left_inverse hinv)]

end Eliminate

/-! ### The stages -/

section Stage

variable [Fintype m] [LinearOrder m] [Field K] [DecidableEq K]

omit [LinearOrder m] in
/-- The candidate pivot rows for column `j`: the rows that are zero before `j` and nonzero at
`j`. -/
@[expose] def pivotCandidates (A : Matrix m (Fin c) K) (j : Fin c) : Finset m :=
  univ.filter fun i => IsFreeBefore A j i ∧ A i j ≠ 0

omit [LinearOrder m] in
theorem mem_pivotCandidates {A : Matrix m (Fin c) K} {j : Fin c} {i : m} :
    i ∈ pivotCandidates A j ↔ IsFreeBefore A j i ∧ A i j ≠ 0 := by
  simp [pivotCandidates]

/-- The pivot row for column `j`: the first row that is zero on the columns before `j` and nonzero
at `j`, or `none` if there is no such row. -/
@[expose] def pivotRow (A : Matrix m (Fin c) K) (j : Fin c) : Option m :=
  if h : (pivotCandidates A j).Nonempty then some ((pivotCandidates A j).min' h) else none

/-- One stage of Gauss–Jordan elimination at column `j`: if column `j` has a pivot row, clear
column `j` in every other row; otherwise leave the matrix unchanged. -/
@[expose] def stage (A : Matrix m (Fin c) K) (j : Fin c) : Matrix m (Fin c) K :=
  (pivotRow A j).elim A (eliminate A j)

/-- The stages for the columns `0, …, k - 1`, in order; indices from `c` on are skipped. -/
@[expose] def reduceUpTo (A : Matrix m (Fin c) K) : ℕ → Matrix m (Fin c) K
  | 0 => A
  | k + 1 => if h : k < c then stage (reduceUpTo A k) ⟨k, h⟩ else reduceUpTo A k

/-- Gauss–Jordan elimination: the stages for all columns, in order. -/
@[expose] def reduce (A : Matrix m (Fin c) K) : Matrix m (Fin c) K :=
  reduceUpTo A c

/-- The pivot row is the first candidate: it is free before `j` and nonzero at `j`, and every
earlier row that is free before `j` is zero at `j`. -/
theorem pivotRow_eq_some_iff {A : Matrix m (Fin c) K} {j : Fin c} {p : m} :
    pivotRow A j = some p ↔
      IsFreeBefore A j p ∧ A p j ≠ 0 ∧ ∀ i < p, IsFreeBefore A j i → A i j = 0 := by
  unfold pivotRow
  split_ifs with h
  · rw [Option.some_inj]
    constructor
    · rintro rfl
      obtain ⟨hfree, hne⟩ := mem_pivotCandidates.mp ((pivotCandidates A j).min'_mem h)
      refine ⟨hfree, hne, fun i hi hfi => ?_⟩
      by_contra hij
      exact absurd ((pivotCandidates A j).min'_le i (mem_pivotCandidates.mpr ⟨hfi, hij⟩))
        (not_le.mpr hi)
    · rintro ⟨hfree, hne, hmin⟩
      refine le_antisymm ((pivotCandidates A j).min'_le p (mem_pivotCandidates.mpr ⟨hfree, hne⟩))
        ((pivotCandidates A j).le_min' h p fun i hi => not_lt.mp fun hip => ?_)
      exact (mem_pivotCandidates.mp hi).2 (hmin i hip (mem_pivotCandidates.mp hi).1)
  · exact iff_of_false (by simp) fun ⟨hfree, hne, _⟩ => h ⟨p, mem_pivotCandidates.mpr ⟨hfree, hne⟩⟩

/-- Column `j` has no pivot row exactly when every row that is free before `j` is zero at `j`. -/
theorem pivotRow_eq_none_iff {A : Matrix m (Fin c) K} {j : Fin c} :
    pivotRow A j = none ↔ ∀ i, IsFreeBefore A j i → A i j = 0 := by
  unfold pivotRow
  split_ifs with h
  · obtain ⟨i, hi⟩ := id h
    obtain ⟨hfree, hne⟩ := mem_pivotCandidates.mp hi
    exact iff_of_false (by simp) fun hall => hne (hall i hfree)
  · refine iff_of_true rfl fun i hfree => ?_
    by_contra hne
    exact h ⟨i, mem_pivotCandidates.mpr ⟨hfree, hne⟩⟩

theorem stage_of_pivotRow_eq_none {A : Matrix m (Fin c) K} {j : Fin c}
    (h : pivotRow A j = none) : stage A j = A := by
  rw [stage, h, Option.elim_none]

theorem stage_of_pivotRow_eq_some {A : Matrix m (Fin c) K} {j : Fin c} {p : m}
    (h : pivotRow A j = some p) : stage A j = eliminate A j p := by
  rw [stage, h, Option.elim_some]

theorem reduceUpTo_zero (A : Matrix m (Fin c) K) : reduceUpTo A 0 = A :=
  rfl

theorem reduceUpTo_succ_of_lt (A : Matrix m (Fin c) K) {k : ℕ} (h : k < c) :
    reduceUpTo A (k + 1) = stage (reduceUpTo A k) ⟨k, h⟩ := by
  rw [reduceUpTo, dite_eq_left h]

theorem reduceUpTo_succ_of_le (A : Matrix m (Fin c) K) {k : ℕ} (h : c ≤ k) :
    reduceUpTo A (k + 1) = reduceUpTo A k := by
  rw [reduceUpTo, dite_eq_right (Nat.not_lt.mpr h)]

/-! ### Rank -/

/-- A stage preserves the rank. -/
theorem rank_stage (A : Matrix m (Fin c) K) (j : Fin c) : (stage A j).rank = A.rank := by
  rcases h : pivotRow A j with _ | p
  · rw [stage_of_pivotRow_eq_none h]
  · rw [stage_of_pivotRow_eq_some h, rank_eliminate]

theorem rank_reduceUpTo (A : Matrix m (Fin c) K) (k : ℕ) : (reduceUpTo A k).rank = A.rank := by
  induction k with
  | zero => rfl
  | succ k ih =>
    by_cases h : k < c
    · rw [reduceUpTo_succ_of_lt A h, rank_stage, ih]
    · rw [reduceUpTo_succ_of_le A (Nat.not_lt.mp h), ih]

/-- Gauss–Jordan elimination preserves the rank. -/
theorem rank_reduce (A : Matrix m (Fin c) K) : (reduce A).rank = A.rank :=
  rank_reduceUpTo A c

/-- A stage extends the invariant by one column. The pivot row is free before `j`, so it changes no
earlier pivot column; it becomes the pivot for column `j`, and every other row is cleared there. -/
private theorem isReducedBefore_stage {A : Matrix m (Fin c) K} {j : Fin c}
    (hA : IsReducedBefore A j.1) : IsReducedBefore (stage A j) (j.1 + 1) := by
  rcases h : pivotRow A j with _ | p
  · rw [stage_of_pivotRow_eq_none h]
    intro i
    rcases hA i with hfree | ⟨l, hl, hne, hcol⟩
    · refine Or.inl fun l hl => ?_
      rcases (Nat.lt_add_one_iff.mp hl).lt_or_eq with hl | hl
      · exact hfree l hl
      · rw [show l = j from Fin.ext hl]
        exact pivotRow_eq_none_iff.mp h i hfree
    · exact Or.inr ⟨l, hl.trans (Nat.lt_add_one _), hne, hcol⟩
  · obtain ⟨hpfree, hpne, -⟩ := pivotRow_eq_some_iff.mp h
    rw [stage_of_pivotRow_eq_some h]
    -- the columns before `j` are unchanged, since the pivot row is zero there
    have hpre : ∀ l : Fin c, l.1 < j.1 → ∀ i, eliminate A j p i l = A i l :=
      fun l hl => eliminate_apply_of_eq_zero (hpfree l hl)
    intro i
    by_cases hip : i = p
    · rw [hip]
      exact Or.inr ⟨j, Nat.lt_add_one _, by rwa [eliminate_apply_self],
        fun i' hi' => eliminate_apply_of_ne_of_ne_zero hpne hi'⟩
    · rcases hA i with hfree | ⟨l, hl, hne, hcol⟩
      · refine Or.inl fun l hl => ?_
        rcases (Nat.lt_add_one_iff.mp hl).lt_or_eq with hl | hl
        · rw [hpre l hl]
          exact hfree l hl
        · rw [show l = j from Fin.ext hl]
          exact eliminate_apply_of_ne_of_ne_zero hpne hip
      · exact Or.inr ⟨l, hl.trans (Nat.lt_add_one _), by rwa [hpre l hl],
          fun i' hi' => by rw [hpre l hl]; exact hcol i' hi'⟩

private theorem isReducedBefore_reduceUpTo (A : Matrix m (Fin c) K) {k : ℕ} (hk : k ≤ c) :
    IsReducedBefore (reduceUpTo A k) k := by
  induction k with
  | zero => exact isReducedBefore_zero A
  | succ k ih =>
    rw [reduceUpTo_succ_of_lt A hk]
    exact isReducedBefore_stage (ih (Nat.le_of_succ_le hk))

/-- Every nonzero row of `reduce A` owns a column: it is nonzero there and every other row is zero
there. Distinct rows own distinct columns, but one row may own several. -/
theorem exists_pivot_of_reduce_ne_zero (A : Matrix m (Fin c) K) {i : m}
    (hi : (reduce A).row i ≠ 0) :
    ∃ l, reduce A i l ≠ 0 ∧ ∀ i', i' ≠ i → reduce A i' l = 0 :=
  exists_pivot_of_isReducedBefore (isReducedBefore_reduceUpTo A le_rfl) hi

/-- A matrix in which every nonzero row owns a column, where every other row is zero, has rank
equal to its number of nonzero rows. One owned column per nonzero row gives a diagonal submatrix
with nonzero diagonal. -/
private theorem rank_eq_card_of_isReducedBefore {B : Matrix m (Fin c) K}
    (hB : IsReducedBefore B c) : B.rank = #{i | B.row i ≠ 0} := by
  refine le_antisymm (rank_le_card_of_support_subset B _ fun i hi =>
    mem_filter.mpr ⟨mem_univ i, hi⟩) ?_
  let N := {i // B.row i ≠ 0}
  choose piv hpiv using fun i : N => exists_pivot_of_isReducedBefore hB i.2
  have hdiag : B.submatrix (fun i : N => i.1) piv = diagonal fun i => B i.1 (piv i) := by
    ext i i'
    by_cases h : i = i'
    · rw [h, submatrix_apply, diagonal_apply_eq]
    · rw [submatrix_apply, diagonal_apply_ne _ h]
      exact (hpiv i').2 i.1 fun h' => h (Subtype.ext h')
  calc #{i | B.row i ≠ 0} = Fintype.card N := (Fintype.card_subtype _).symm
    _ = (diagonal fun i => B i.1 (piv i)).rank := by
        rw [rank_diagonal]
        exact (Fintype.card_congr (Equiv.subtypeUnivEquiv fun i => (hpiv i).1)).symm
    _ ≤ B.rank := by
        rw [← hdiag]
        exact rank_submatrix_le B _ _

/-- **Rank by Gauss–Jordan elimination**: the rank of `A` is the number of nonzero rows of
`reduce A`. Each nonzero row owns a column where every other row is zero
(`exists_pivot_of_reduce_ne_zero`), and these give a diagonal submatrix of full size. -/
theorem rank_eq_card_reduce_ne_zero (A : Matrix m (Fin c) K) :
    A.rank = #{i | (reduce A).row i ≠ 0} := by
  rw [← rank_reduce A]
  exact rank_eq_card_of_isReducedBefore (isReducedBefore_reduceUpTo A le_rfl)

end Stage

/-! ### Over `ZMod 2` -/

section ZModTwo

variable [Fintype m] [LinearOrder m]

/-- Over `ZMod 2` a stage needs no division. The pivot entry is `1`, and the stage adds the pivot
row `p` to every other row `i` with `A i j = 1`. Each entry is a sum of products of entries and
pivot indicators, which a Boolean circuit evaluates with XOR and AND gates. -/
theorem stage_apply_zmod_two (A : Matrix m (Fin c) (ZMod 2)) (j : Fin c) (i : m) (l : Fin c) :
    stage A j i l =
      A i l + ∑ p, if pivotRow A j = some p ∧ p ≠ i then A i j * A p l else 0 := by
  rcases h : pivotRow A j with _ | p
  · simp [stage_of_pivotRow_eq_none h]
  · have hp1 : A p j = 1 := by
      have key : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
      exact key _ (pivotRow_eq_some_iff.mp h).2.1
    rw [stage_of_pivotRow_eq_some h,
      sum_eq_single p (fun q _ hq => by simp [Ne.symm hq]) (by simp)]
    by_cases hip : i = p
    · subst hip
      simp [eliminate_apply_self]
    · rw [eliminate_apply_of_ne hip, hp1, div_one, ite_eq_left ⟨rfl, Ne.symm hip⟩, sub_eq_add_neg,
        ZMod.neg_eq_self_mod_two]

end ZModTwo

end Matrix.GaussJordan
