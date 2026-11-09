/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.Int.Cramer
public import Mathlib.LinearAlgebra.Matrix.Rank
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import Mathlib.Data.List.GetD
import CslibFrontier.Foundations.Data.List.OfFn
import CslibFrontier.Foundations.Data.Int.Order

/-!
# Binary original-row selection by Gram determinants

`gramRowBasis` scans original integer rows and retains a row exactly when its
addition leaves the row Gram determinant nonzero. This is a division-free
alternative to the rectangular elimination step of [ChenJiangZhu2027], Lemma 3.1,
PDF pp. 10–11. It tests one matrix per original row, rather than enumerating minors.
The column count is supplied in unary; missing entries are zero and excess columns
are ignored. No basis or arithmetic-cost certificate is supplied as input.

The source lemma accepts rational entries and selects an augmented row basis even
for inconsistent systems. This API specializes to integer coefficients, selects a
coefficient row basis, and preserves equations under consistency. The companion
rectangular solver detects inconsistency by checking its actual recovered point;
it does not claim an equivalent selected subsystem on inconsistent inputs.

## Main results

* `gramRowBasis_independent`, `gramRowBasis_span`: the executed scan selects a row basis.
* `gramRowBasis_rank`: the computed length equals the rational row-space dimension.
* `gramRowBasis_polytime`: uniform binary polynomial time, including determinant arithmetic.
* `rowGram_stage_bits_le`: explicit control of intermediate determinant coefficients.

## Main definitions

* `rowGram`: the integer Gram table on selected original row indices.
* `gramRowBasis`: greedy original-row selection.
-/

public section

namespace Cslib.LinearSystem

open Matrix Circuits.Rational Turing.MultiTapeTM

/-- Materialize the Gram matrix of selected original rows on `n` declared columns. -/
@[expose] def rowGram (n : ℕ) (A : List (List ℤ)) (ids : List ℕ) : List (List ℤ) :=
  tabulateTable ids.length ids.length fun i j =>
    ((List.range n).map fun c => rowEntry A (ids.getD i 0) c *
      rowEntry A (ids.getD j 0) c).sum

/-- Retain a row when adjoining it preserves row independence. -/
@[expose] def gramRowStep (n : ℕ) (A : List (List ℤ)) (ids : List ℕ) (i : ℕ) : List ℕ :=
  if detRows (rowGram n A (i :: ids)) = 0 then ids else i :: ids

/-- One greedy scan of the original rows; the output contains original indices. -/
@[expose] def gramRowBasis (n : ℕ) (A : List (List ℤ)) : List ℕ :=
  (List.range A.length).foldl (gramRowStep n A) []

/-- The rational rows denoted by an original-index list. -/
@[expose] def indexedRows (n : ℕ) (A : List (List ℤ)) (ids : List ℕ) :
    Matrix (Fin ids.length) (Fin n) ℚ :=
  fun i j => rowEntry A (ids.getD i 0) j

/-- Gram construction is uniform in the matrix, index list and declared width. -/
@[fun_prop] theorem computableInPolyTime_rowGram
    {α : Type} {enc : α ↪ List Bool} {n : α → ℕ} {A : α → List (List ℤ)}
    {ids : α → List ℕ}
    (hn : ComputableInPolyTime n enc encUnary)
    (hA : ComputableInPolyTime A enc (encList (encList encIntBin)))
    (hi : ComputableInPolyTime ids enc (encList encUnary)) :
    ComputableInPolyTime (fun x => rowGram (n x) (A x) (ids x))
      enc (encList (encList encIntBin)) := by
  unfold rowGram
  apply computableInPolyTime_tabulateTable (by fun_prop) (by fun_prop)
  dsimp only [TableIndex.ctx, TableIndex.row, TableIndex.col, TableIndex.rowCtx]
  fun_prop

/-- A row-independence test includes all binary determinant arithmetic. -/
@[fun_prop] theorem computableInPolyTime_gramRowStep
    {α : Type} {enc : α ↪ List Bool} {n : α → ℕ} {A : α → List (List ℤ)}
    {ids : α → List ℕ} {i : α → ℕ}
    (hn : ComputableInPolyTime n enc encUnary)
    (hA : ComputableInPolyTime A enc (encList (encList encIntBin)))
    (hs : ComputableInPolyTime ids enc (encList encUnary))
    (hi : ComputableInPolyTime i enc encUnary) :
    ComputableInPolyTime (fun x => gramRowStep (n x) (A x) (ids x) (i x))
      enc (encList encUnary) := by
  unfold gramRowStep
  fun_prop

/-- The whole row scan is polynomial-time on unary width and framed binary integer
rows. The accumulator stores only original unary indices, growing by one index per
input row; determinant intermediate sizes are covered by `detRows_polytime`. -/
@[fun_prop] theorem gramRowBasis_polytime :
    ComputableInPolyTime (fun p : ℕ × List (List ℤ) => gramRowBasis p.1 p.2)
      (encPair encUnary (encList (encList encIntBin))) (encList encUnary) := by
  unfold gramRowBasis
  refine ComputableInPolyTime.foldlWith_of_bounded_growth
    (par := fun p : ℕ × List (List ℤ) => p)
    (encP := encPair encUnary (encList (encList encIntBin)))
    (encA := encUnary) (by fun_prop) (by fun_prop) (by fun_prop)
    (step := fun p ids i => gramRowStep p.1 p.2 ids i) (by fun_prop)
    (growth := fun p => 2 * p.2.length + 1) (by
      have hl : PolyBounded (fun p : ℕ × List (List ℤ) =>
          ((encPair encUnary (encList (encList encIntBin))) p).length)
          (fun p => p.2.length) :=
        (show ComputableInPolyTime (fun p : ℕ × List (List ℤ) => p.2.length)
          (encPair encUnary (encList (encList encIntBin))) encUnary from by fun_prop).polyBounded
      exact ((PolyBounded.const 2).mul hl).add (PolyBounded.const 1)) ?_
  intro p ids i hi
  have hi' : i < p.2.length := List.mem_range.mp hi
  unfold gramRowStep
  split_ifs
  · omega
  · simp only [encList_cons, List.length_append, length_frame, encUnary_apply,
      List.length_replicate]
    omega

/-- The list program computes the ordinary row Gram determinant over the rationals. -/
theorem rowGram_det (n : ℕ) (A : List (List ℤ)) (ids : List ℕ) :
    (detRows (rowGram n A ids) : ℚ) =
      (indexedRows n A ids * (indexedRows n A ids)ᵀ).det := by
  have he : detRows (rowGram n A ids) =
      Matrix.det (Matrix.of fun i j : Fin ids.length => ((List.range n).map fun c =>
        rowEntry A (ids.getD i 0) c * rowEntry A (ids.getD j 0) c).sum) := by
    apply detRows_eq_det_of_rowEntry
    · simp [rowGram]
    · intro i j
      simp [rowGram, rowEntry_tabulateTable, i.isLt, j.isLt]
  rw [he]
  change (Int.castRingHom ℚ) _ = _
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [indexedRows, Matrix.mul_apply, List.sum_map_range]

/-- Nonzero Gram determinant is exactly rational row independence. -/
theorem rowGram_ne_zero_iff (n : ℕ) (A : List (List ℤ)) (ids : List ℕ) :
    detRows (rowGram n A ids) ≠ 0 ↔ LinearIndependent ℚ (indexedRows n A ids).row := by
  have hg : (detRows (rowGram n A ids) : ℚ) ≠ 0 ↔
      detRows (rowGram n A ids) ≠ 0 := by exact_mod_cast Iff.rfl
  rw [← hg, rowGram_det]
  rw [← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det,
    ← Matrix.mulVec_injective_iff_isUnit]
  change Function.Injective (indexedRows n A ids * (indexedRows n A ids)ᵀ).mulVecLin ↔ _
  rw [← LinearMap.ker_eq_bot]
  rw [show indexedRows n A ids * (indexedRows n A ids)ᵀ =
      ((indexedRows n A ids)ᵀ)ᵀ * (indexedRows n A ids)ᵀ by rw [transpose_transpose],
    Matrix.ker_mulVecLin_transpose_mul_self, LinearMap.ker_eq_bot]
  change Function.Injective (fun v => (indexedRows n A ids)ᵀ *ᵥ v) ↔ _
  simp_rw [Matrix.mulVec_transpose]
  exact Matrix.vecMul_injective_iff

/-- Every partial sum used to construct a Gram entry has polynomially bounded
binary width, even before the determinant routine is called. -/
theorem rowGram_partial_sum_natAbs_lt (n : ℕ) (A : List (List ℤ)) (ids : List ℕ)
    (β i j k : ℕ) (hA : ∀ i j, (rowEntry A i j).natAbs < 2 ^ β) :
    ((((List.range n).map fun c => rowEntry A (ids.getD i 0) c *
      rowEntry A (ids.getD j 0) c).take k).sum).natAbs < 2 ^ (n + 2 * β) := by
  have hs := List.natAbs_sum_take_le_length_mul
    (l := (List.range n).map fun c => rowEntry A (ids.getD i 0) c *
      rowEntry A (ids.getD j 0) c) (C := 2 ^ β * 2 ^ β) (by
      intro z hz
      obtain ⟨c, _, rfl⟩ := List.mem_map.mp hz
      rw [Int.natAbs_mul]
      exact Nat.mul_le_mul (hA _ _).le (hA _ _).le) k
  simp only [List.length_map, List.length_range] at hs
  calc _ ≤ n * (2 ^ β * 2 ^ β) := hs
       _ < 2 ^ n * (2 ^ β * 2 ^ β) :=
         Nat.mul_lt_mul_of_pos_right (Nat.lt_two_pow_self (n := n)) (by positivity)
       _ = 2 ^ (n + 2 * β) := by rw [pow_add, two_mul, pow_add]

/-- Uniform magnitude control on all Gram entries, including default zero reads. -/
theorem rowGram_natAbs_lt (n : ℕ) (A : List (List ℤ)) (ids : List ℕ) (β : ℕ)
    (hA : ∀ i j, (rowEntry A i j).natAbs < 2 ^ β) (i j : ℕ) :
    (rowEntry (rowGram n A ids) i j).natAbs < 2 ^ (n + 2 * β) := by
  simp only [rowGram, rowEntry_tabulateTable]
  split_ifs
  · have h := rowGram_partial_sum_natAbs_lt n A ids β i j n hA
    rw [List.take_of_length_le (by simp)] at h
    exact h
  · exact Nat.two_pow_pos _

/-- All Bird-stage coefficients in every row-independence test have controlled
bit width. Selected rows are never repeatedly multiplied into a growing rational
elimination table. The determinant module also bounds its internal products/sums. -/
theorem rowGram_stage_bits_le (n : ℕ) (A : List (List ℤ)) (ids : List ℕ) (β k i j : ℕ)
    (hA : ∀ i j, (rowEntry A i j).natAbs < 2 ^ β) :
    intBits (rowEntry (stagesRows (rowGram n A ids) k) i j) ≤
      n + 2 * β + k * (1 + ids.length + (n + 2 * β)) + 1 := by
  have h := intBits_rowEntry_stagesRows_le (A := rowGram n A ids)
    (fun i j => (intBits_le_iff _ _).mpr (rowGram_natAbs_lt n A ids β hA i j)) k i j
  simpa [rowGram] using h

private theorem indexedRows_cons (n : ℕ) (A : List (List ℤ)) (ids : List ℕ) (i : ℕ) :
    (indexedRows n A (i :: ids)).row =
      Fin.cons (fun j : Fin n => (rowEntry A i j : ℚ)) (indexedRows n A ids).row := by
  funext k j
  refine Fin.cases ?_ (fun k => ?_) k <;>
    simp [indexedRows, Matrix.row, List.getD_eq_getElem?_getD, Fin.cons, Fin.cases]

private theorem indexedRows_range (n : ℕ) (A : List (List ℤ)) (ids : List ℕ) :
    Set.range (indexedRows n A ids).row =
      (fun i => fun j : Fin n => (rowEntry A i j : ℚ)) '' {i | i ∈ ids} := by
  ext v
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨ids[i], List.getElem_mem i.isLt, ?_⟩
    funext j
    simp [indexedRows, Matrix.row, List.getD_eq_getElem?_getD]
  · rintro ⟨i, hi, rfl⟩
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hi
    refine ⟨⟨k, hk⟩, ?_⟩
    funext j
    simp [indexedRows, Matrix.row, List.getD_eq_getElem?_getD, hk]

private theorem indexedRows_range_cons (n : ℕ) (A : List (List ℤ)) (ids : List ℕ) (i : ℕ) :
    Set.range (indexedRows n A (i :: ids)).row =
      insert (fun j : Fin n => (rowEntry A i j : ℚ)) (Set.range (indexedRows n A ids).row) := by
  rw [indexedRows_cons, Fin.range_cons]

private theorem gramRowStep_independent (n : ℕ) (A : List (List ℤ)) (ids : List ℕ) (i : ℕ)
    (hs : LinearIndependent ℚ (indexedRows n A ids).row) :
    LinearIndependent ℚ (indexedRows n A (gramRowStep n A ids i)).row := by
  by_cases h : detRows (rowGram n A (i :: ids)) = 0
  · rw [show gramRowStep n A ids i = ids from by simp [gramRowStep, h]]
    exact hs
  · rw [show gramRowStep n A ids i = i :: ids from by simp [gramRowStep, h]]
    exact (rowGram_ne_zero_iff n A (i :: ids)).mp h

private theorem gramRowStep_span (n : ℕ) (A : List (List ℤ)) (ids : List ℕ) (i : ℕ)
    (hs : LinearIndependent ℚ (indexedRows n A ids).row) :
    Submodule.span ℚ (Set.range (indexedRows n A (gramRowStep n A ids i)).row) =
      Submodule.span ℚ (insert (fun j : Fin n => (rowEntry A i j : ℚ))
        (Set.range (indexedRows n A ids).row)) := by
  by_cases h : detRows (rowGram n A (i :: ids)) = 0
  · rw [show gramRowStep n A ids i = ids from by simp [gramRowStep, h]]
    have hn : ¬ LinearIndependent ℚ (indexedRows n A (i :: ids)).row := by
      rw [← rowGram_ne_zero_iff, h]
      simp
    rw [indexedRows_cons, linearIndependent_finCons] at hn
    have hm : (fun j : Fin n => (rowEntry A i j : ℚ)) ∈
        Submodule.span ℚ (Set.range (indexedRows n A ids).row) := by tauto
    exact (Submodule.span_insert_eq_span hm).symm
  · rw [show gramRowStep n A ids i = i :: ids from by simp [gramRowStep, h],
      indexedRows_range_cons]

private theorem gramRowFold_independent (n : ℕ) (A : List (List ℤ)) (rows ids : List ℕ)
    (hs : LinearIndependent ℚ (indexedRows n A ids).row) :
    LinearIndependent ℚ (indexedRows n A (rows.foldl (gramRowStep n A) ids)).row := by
  induction rows generalizing ids with
  | nil => exact hs
  | cons i rows ih => exact ih _ (gramRowStep_independent n A ids i hs)

private theorem gramRowFold_span (n : ℕ) (A : List (List ℤ)) (rows ids : List ℕ)
    (hs : LinearIndependent ℚ (indexedRows n A ids).row) :
    Submodule.span ℚ (Set.range (indexedRows n A (rows.foldl (gramRowStep n A) ids)).row) =
      Submodule.span ℚ ((Set.range (indexedRows n A ids).row) ∪
        ((fun i => fun j : Fin n => (rowEntry A i j : ℚ)) '' {i | i ∈ rows})) := by
  induction rows generalizing ids with
  | nil => simp
  | cons i rows ih =>
    rw [List.foldl_cons, ih _ (gramRowStep_independent n A ids i hs), Submodule.span_union,
      gramRowStep_span n A ids i hs]
    simp only [Submodule.span_insert, List.mem_cons,
      Set.ofPred_or, Set.ofPred_eq_eq_singleton, Set.image_union, Set.image_singleton,
      Submodule.span_union]
    ac_rfl

private theorem gramRowFold_mem (n : ℕ) (A : List (List ℤ)) (rows ids : List ℕ) :
    ∀ i ∈ rows.foldl (gramRowStep n A) ids, i ∈ ids ∨ i ∈ rows := by
  induction rows generalizing ids with
  | nil => simp
  | cons j rows ih =>
    intro i hi
    have h := ih (gramRowStep n A ids j) i hi
    unfold gramRowStep at h
    split_ifs at h <;> simp only [List.mem_cons] at * <;> tauto

private theorem indexedRows_empty (n : ℕ) (A : List (List ℤ)) :
    LinearIndependent ℚ (indexedRows n A []).row := by
  change LinearIndependent ℚ (fun i : Fin 0 => fun j : Fin n =>
    (rowEntry A (([] : List ℕ).getD i 0) j : ℚ))
  exact linearIndependent_empty_type

/-- The selected coefficient rows are rationally independent, including empty and
rank-deficient inputs. This is proved about the actual determinant-based scan. -/
theorem gramRowBasis_independent (n : ℕ) (A : List (List ℤ)) :
    LinearIndependent ℚ (indexedRows n A (gramRowBasis n A)).row :=
  gramRowFold_independent n A _ [] (indexedRows_empty n A)

/-- Every emitted index names an original input row. -/
theorem gramRowBasis_mem (n : ℕ) (A : List (List ℤ)) (i : ℕ)
    (hi : i ∈ gramRowBasis n A) : i < A.length := by
  have h := gramRowFold_mem n A (List.range A.length) [] i hi
  simpa using h

/-- The selected original rows span exactly the original rational row space. -/
theorem gramRowBasis_span (n : ℕ) (A : List (List ℤ)) :
    Submodule.span ℚ (Set.range (indexedRows n A (gramRowBasis n A)).row) =
      Submodule.span ℚ (Set.range (fun i : Fin A.length =>
        fun j : Fin n => (rowEntry A i j : ℚ))) := by
  have h := gramRowFold_span n A (List.range A.length) [] (indexedRows_empty n A)
  have hr : ((fun i => fun j : Fin n => (rowEntry A i j : ℚ)) ''
      {i | i ∈ List.range A.length}) = Set.range (fun i : Fin A.length =>
        fun j : Fin n => (rowEntry A i j : ℚ)) := by
    ext v
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, List.mem_range.mp hi⟩, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i, List.mem_range.mpr i.isLt, rfl⟩
  simpa only [gramRowBasis, indexedRows_range, List.not_mem_nil, Set.ofPred_false,
    Set.image_empty, Set.empty_union, hr] using h

/-- There are at most as many selected rows as declared columns. -/
theorem gramRowBasis_length (n : ℕ) (A : List (List ℤ)) :
    (gramRowBasis n A).length ≤ n := by
  simpa using (gramRowBasis_independent n A).fintype_card_le_finrank

/-- The executable selected count is the dimension of the original coefficient row
space, rather than merely an upper bound on the number of pivots. -/
theorem gramRowBasis_rank (n : ℕ) (A : List (List ℤ)) :
    (gramRowBasis n A).length = Module.finrank ℚ
      (Submodule.span ℚ (Set.range (fun i : Fin A.length =>
        fun j : Fin n => (rowEntry A i j : ℚ)))) := by
  rw [← gramRowBasis_span, finrank_span_eq_card (gramRowBasis_independent n A)]
  simp

/-- On a consistent system, the computed original subsystem has exactly the same
rational solutions. The witness is used only in this semantic theorem; the scan
itself takes no solution or consistency advice. -/
theorem gramRowBasis_selected_iff (n : ℕ) (A : List (List ℤ)) (b : List ℤ)
    (x₀ : Fin n → ℚ)
    (hx₀ : ∀ i : Fin A.length, (fun j : Fin n => (rowEntry A i j : ℚ)) ⬝ᵥ x₀ = b.getD i 0)
    (x : Fin n → ℚ) :
    (∀ i : Fin (gramRowBasis n A).length,
      (indexedRows n A (gramRowBasis n A)).row i ⬝ᵥ x =
        b.getD ((gramRowBasis n A).getD i 0) 0) ↔
      ∀ i : Fin A.length, (fun j : Fin n => (rowEntry A i j : ℚ)) ⬝ᵥ x = b.getD i 0 := by
  constructor
  · intro hx
    let L : (Fin n → ℚ) →ₗ[ℚ] ℚ :=
      { toFun := fun v => v ⬝ᵥ x - v ⬝ᵥ x₀
        map_add' := by intro u v; simp [add_dotProduct]; ring
        map_smul' := by intro c v; simp [smul_dotProduct, mul_sub] }
    have hker : Submodule.span ℚ (Set.range
        (indexedRows n A (gramRowBasis n A)).row) ≤ L.ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      have hi : (gramRowBasis n A).getD i 0 < A.length := by
        apply gramRowBasis_mem n A
        rw [List.getD_eq_getElem _ _ i.isLt]
        exact List.getElem_mem i.isLt
      change (indexedRows n A (gramRowBasis n A)).row i ⬝ᵥ x -
        (indexedRows n A (gramRowBasis n A)).row i ⬝ᵥ x₀ = 0
      rw [hx i]
      exact sub_eq_zero.mpr (hx₀ ⟨_, hi⟩).symm
    rw [gramRowBasis_span] at hker
    intro i
    have h := hker (Submodule.subset_span (Set.mem_range_self i))
    change (fun j : Fin n => (rowEntry A i j : ℚ)) ⬝ᵥ x -
      (fun j : Fin n => (rowEntry A i j : ℚ)) ⬝ᵥ x₀ = 0 at h
    rw [hx₀] at h
    exact sub_eq_zero.mp h
  · intro hx i
    have hi : (gramRowBasis n A).getD i 0 < A.length := by
      apply gramRowBasis_mem n A
      rw [List.getD_eq_getElem _ _ i.isLt]
      exact List.getElem_mem i.isLt
    exact hx ⟨_, hi⟩

end Cslib.LinearSystem
