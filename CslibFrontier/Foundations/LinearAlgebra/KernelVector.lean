/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Module.BigOperators

/-!
# A kernel vector by elimination

Let `A` be a matrix with `r` rows and `n` columns over a field. Gaussian elimination finds a
nonzero vector `v` with `A v = 0` whenever one exists. This module records a branch-free variant
that suits circuits: it maintains `n` vectors `N i` spanning the common kernel of the rows
processed so far, starting from the unit vectors. To process a row `a` it computes the values
`b i = a ⬝ N i`, takes the first index `j` with `b j ≠ 0` (the *pivot*), and replaces each `N i`
by `N i - (b i / b j) • N j`. The new vectors are killed by `a`, and every vector of the old span
killed by `a` lies in their span (`Cslib.LinearAlgebra.kernelStep`). When `b = 0` no pivot exists;
the pivot value and pivot vector are then zero, and since division by zero is zero in a field the
update leaves `N` unchanged. After all rows the vectors span the kernel of `A`
(`Cslib.LinearAlgebra.kernelBasis`), and the first nonzero one is the output
(`Cslib.LinearAlgebra.kernelVec`): it lies in the kernel (`Cslib.LinearAlgebra.mulVec_kernelVec`)
and it is nonzero whenever the kernel is (`Cslib.LinearAlgebra.kernelVec_ne_zero`).

Pivots are selected by the indicator `Cslib.LinearAlgebra.firstFlags b` of the first nonzero entry
of `b`, so every step is a fixed arithmetic expression in the entries, with tests for zero and no
other branching. Processing a row costs `O(n ^ 2)` field operations. The procedure is Gaussian
elimination organized for straight-line evaluation, as needed to count its gates in circuits.

## Main definitions

* `Cslib.LinearAlgebra.firstFlags`: the indicator of the first nonzero entry.
* `Cslib.LinearAlgebra.firstNonzero`: the first nonzero entry of a vector, as a value.
* `Cslib.LinearAlgebra.rowValues`: the values `a ⬝ N i` of a row on the vectors of the family.
* `Cslib.LinearAlgebra.pivotVec`: the pivot vector, the member of the family at the first nonzero
  row value, or zero.
* `Cslib.LinearAlgebra.kernelStep`: process one row.
* `Cslib.LinearAlgebra.kernelBasisUpTo`: process the first `k` rows, starting from the unit
  vectors.
* `Cslib.LinearAlgebra.kernelBasis`: process all rows, starting from the unit vectors.
* `Cslib.LinearAlgebra.kernelVec`: the first nonzero vector of the final family.

## Main results

* `Cslib.LinearAlgebra.mulVec_kernelVec`: the output lies in the kernel.
* `Cslib.LinearAlgebra.kernelVec_ne_zero`: the output is nonzero when the kernel is nontrivial.

## References

* [P. Bürgisser, M. Clausen, M. A. Shokrollahi, *Algebraic Complexity Theory*]
  [BurgisserClausenShokrollahi1997]
* [M. Sudan, L. Trevisan, S. Vadhan, *Pseudorandom generators without the XOR lemma*]
  [SudanTrevisanVadhan2001]
-/

@[expose] public section

namespace Cslib.LinearAlgebra

open Finset
open scoped Matrix

variable {F : Type*} [Field F] [DecidableEq F] {n r : ℕ}

/-! ### The first nonzero entry -/

/-- `firstFlags b i` is one at the first index `i` with `b i ≠ 0` and zero elsewhere; it is zero
everywhere when `b = 0`. -/
def firstFlags (b : Fin n → F) (i : Fin n) : F :=
  if b i ≠ 0 ∧ ∀ i' < i, b i' = 0 then 1 else 0

/-- The flags of the zero vector are zero. -/
theorem firstFlags_of_eq_zero {b : Fin n → F} (hb : b = 0) : firstFlags b = 0 := by
  funext i
  simp [firstFlags, hb]

/-- For `b ≠ 0`, `firstFlags b` is the indicator of the first index `j` with `b j ≠ 0`. -/
theorem exists_firstFlags_eq_single {b : Fin n → F} (hb : b ≠ 0) :
    ∃ j, b j ≠ 0 ∧ (∀ i < j, b i = 0) ∧ firstFlags b = Pi.single j 1 := by
  have hne : (univ.filter fun i => b i ≠ 0).Nonempty := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hb
    exact ⟨i, mem_filter.2 ⟨mem_univ i, hi⟩⟩
  set j := (univ.filter fun i => b i ≠ 0).min' hne
  have hj : b j ≠ 0 := (mem_filter.1 (min'_mem _ hne)).2
  have hmin : ∀ i, b i ≠ 0 → j ≤ i := fun i hi => min'_le _ i (mem_filter.2 ⟨mem_univ i, hi⟩)
  refine ⟨j, hj, fun i hi => by_contra fun h => absurd (hmin i h) (not_le.2 hi),
    funext fun i => ?_⟩
  by_cases hij : i = j
  · subst hij
    simp only [firstFlags, Pi.single_eq_same]
    rw [ite_eq_left ⟨hj, fun i' hi' => by_contra fun h => absurd (hmin i' h) (not_le.2 hi')⟩]
  · rw [Pi.single_eq_of_ne hij, firstFlags, ite_eq_right]
    rintro ⟨hi, hlt⟩
    rcases lt_or_gt_of_ne hij with h | h
    · exact absurd (hmin i hi) (not_le.2 h)
    · exact hj (hlt j h)

/-- Weighting a family by `firstFlags b` selects its member at the first nonzero entry of `b`,
or gives zero when `b = 0`. -/
theorem sum_firstFlags_smul_eq {M : Type*} [AddCommMonoid M] [Module F M] (b : Fin n → F)
    (g : Fin n → M) :
    (b = 0 ∧ ∑ i, firstFlags b i • g i = 0) ∨
      ∃ j, b j ≠ 0 ∧ (∀ i < j, b i = 0) ∧ ∑ i, firstFlags b i • g i = g j := by
  by_cases hb : b = 0
  · exact Or.inl ⟨hb, by simp [firstFlags_of_eq_zero hb]⟩
  · obtain ⟨j, hj, hlt, hflags⟩ := exists_firstFlags_eq_single hb
    refine Or.inr ⟨j, hj, hlt, ?_⟩
    rw [hflags, Finset.sum_eq_single j (fun i _ hij => by rw [Pi.single_eq_of_ne hij, zero_smul])
      (fun h => absurd (mem_univ j) h), Pi.single_eq_same, one_smul]

/-! ### The first nonzero entry as a value -/

/-- The first nonzero entry of a vector, or zero for the zero vector. -/
def firstNonzero (u : Fin n → F) : F := ∑ i, firstFlags u i * u i

/-- The first nonzero entry vanishes only for the zero vector. -/
theorem firstNonzero_eq_zero_iff {u : Fin n → F} : firstNonzero u = 0 ↔ u = 0 := by
  rcases sum_firstFlags_smul_eq u u with ⟨hu, hsum⟩ | ⟨j, hj, -, hsum⟩
  · simp only [smul_eq_mul] at hsum
    exact ⟨fun _ => hu, fun _ => hsum⟩
  · simp only [smul_eq_mul] at hsum
    rw [firstNonzero, hsum]
    exact ⟨fun h => absurd h hj, fun h => absurd (congrFun h j) hj⟩

/-- Scaling by a nonzero constant does not move the first nonzero entry. -/
private theorem firstFlags_smul {c : F} (hc : c ≠ 0) (u : Fin n → F) :
    firstFlags (c • u) = firstFlags u := by
  funext i
  simp [firstFlags, hc]

/-- Scaling a vector scales its first nonzero entry. -/
theorem firstNonzero_smul (c : F) (u : Fin n → F) : firstNonzero (c • u) = c * firstNonzero u := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp [firstNonzero, firstFlags]
  · simp only [firstNonzero, firstFlags_smul hc, Pi.smul_apply, smul_eq_mul, mul_sum]
    exact sum_congr rfl fun i _ => mul_left_comm _ _ _

/-- A vector `u` is `firstNonzero u` times its normalization `(firstNonzero u)⁻¹ • u`. -/
theorem firstNonzero_smul_inv_smul {u : Fin n → F} :
    firstNonzero u • (firstNonzero u)⁻¹ • u = u := by
  by_cases hu : u = 0
  · subst hu; simp
  · exact smul_inv_smul₀ (firstNonzero_eq_zero_iff.not.2 hu) u

/-! ### Elimination -/

/-- The values `a ⬝ N i` of the row `a` on the vectors of the family. -/
def rowValues (a : Fin n → F) (N : Fin n → Fin n → F) (i : Fin n) : F := a ⬝ᵥ N i

/-- The pivot vector: the member of the family at the first nonzero row value, or zero. -/
def pivotVec (a : Fin n → F) (N : Fin n → Fin n → F) : Fin n → F :=
  ∑ i, firstFlags (rowValues a N) i • N i

/-- **One elimination step.** Replace each vector `N i` of the family by
`N i - (b i / β) • P`, where `b` are the row values, `P` the pivot vector and `β = a ⬝ P` the
pivot value. -/
def kernelStep (a : Fin n → F) (N : Fin n → Fin n → F) (i : Fin n) : Fin n → F :=
  N i - (rowValues a N i / (a ⬝ᵥ pivotVec a N)) • pivotVec a N

/-- The family after processing the first `k` rows of `A`, starting from the unit vectors. -/
def kernelBasisUpTo (A : Matrix (Fin r) (Fin n) F) : ℕ → Fin n → Fin n → F
  | 0 => fun i => Pi.single i 1
  | k + 1 =>
    if h : k < r then kernelStep (A ⟨k, h⟩) (kernelBasisUpTo A k) else kernelBasisUpTo A k

/-- The family after processing all rows of `A`; its span is the kernel of `A`. -/
def kernelBasis (A : Matrix (Fin r) (Fin n) F) : Fin n → Fin n → F := kernelBasisUpTo A r

/-- **A kernel vector.** The first nonzero vector of `kernelBasis A`, or zero if all of them are
zero. -/
def kernelVec (A : Matrix (Fin r) (Fin n) F) : Fin n → F :=
  ∑ i, firstFlags (fun i => if kernelBasis A i = 0 then (0 : F) else 1) i • kernelBasis A i

/-! ### Correctness -/

/-- The family `N` spans exactly the vectors killed by the rows in `R`: each member is killed by
every row of `R`, and every vector killed by all of them is a combination of the members. -/
private structure SpansKernel (R : Set (Fin n → F)) (N : Fin n → Fin n → F) : Prop where
  /-- Every member of the family is killed by every row. -/
  dotProduct_eq_zero : ∀ a ∈ R, ∀ i, a ⬝ᵥ N i = 0
  /-- Every vector killed by all rows is a combination of the members. -/
  exists_eq_sum : ∀ v, (∀ a ∈ R, a ⬝ᵥ v = 0) → ∃ c : Fin n → F, v = ∑ i, c i • N i

omit [DecidableEq F] in
/-- The unit vectors span the kernel of the empty set of rows. -/
private theorem spansKernel_single : SpansKernel (∅ : Set (Fin n → F)) fun i => Pi.single i 1 where
  dotProduct_eq_zero := by simp
  exists_eq_sum v _ := ⟨v, by
    funext l
    simp [Finset.sum_apply, Pi.single_apply]⟩

/-- The pivot value `a ⬝ P` is zero only when all row values are zero. -/
private theorem rowValues_eq_zero_of_pivot (a : Fin n → F) (N : Fin n → Fin n → F)
    (h : a ⬝ᵥ pivotVec a N = 0) (i : Fin n) : rowValues a N i = 0 := by
  rcases sum_firstFlags_smul_eq (rowValues a N) N with ⟨hb, -⟩ | ⟨j, hj, -, hP⟩
  · exact congrFun hb i
  · exact absurd (by rwa [pivotVec, hP] at h) hj

/-- **One elimination step is correct.** If `N` spans the kernel of the rows `R`, then
`kernelStep a N` spans the kernel of the rows `R` and `a`. -/
private theorem SpansKernel.kernelStep {R : Set (Fin n → F)} {N : Fin n → Fin n → F}
    (hN : SpansKernel R N) (a : Fin n → F) :
    SpansKernel (insert a R) (Cslib.LinearAlgebra.kernelStep a N) where
  dotProduct_eq_zero a' ha' i := by
    have hP : pivotVec a N = ∑ j, firstFlags (rowValues a N) j • N j := rfl
    rcases Set.mem_insert_iff.1 ha' with rfl | ha'
    · simp only [Cslib.LinearAlgebra.kernelStep, dotProduct_sub, dotProduct_smul, smul_eq_mul]
      by_cases hβ : a' ⬝ᵥ pivotVec a' N = 0
      · rw [rowValues_eq_zero_of_pivot a' N hβ i, zero_div, zero_mul, sub_zero]
        exact rowValues_eq_zero_of_pivot a' N hβ i
      · rw [div_mul_cancel₀ _ hβ, rowValues, sub_self]
    · simp only [Cslib.LinearAlgebra.kernelStep, dotProduct_sub, dotProduct_smul, smul_eq_mul,
        hN.dotProduct_eq_zero a' ha' i, hP, dotProduct_sum, dotProduct_smul,
        hN.dotProduct_eq_zero a' ha', sum_const_zero, mul_zero, sub_zero]
  exists_eq_sum v hv := by
    obtain ⟨c, rfl⟩ := hN.exists_eq_sum v fun a' ha' => hv a' (Set.mem_insert_of_mem a ha')
    refine ⟨c, ?_⟩
    have hav : ∑ i, c i * rowValues a N i = 0 := by
      have := hv a (Set.mem_insert a R)
      simpa [rowValues, dotProduct_sum, dotProduct_smul] using this
    simp only [Cslib.LinearAlgebra.kernelStep, smul_sub, sum_sub_distrib, smul_smul]
    rw [← Finset.sum_smul]
    have : ∑ i, c i * (rowValues a N i / (a ⬝ᵥ pivotVec a N)) = 0 := by
      simp_rw [mul_div_assoc', ← sum_div, hav, zero_div]
    rw [this, zero_smul, sub_zero]

/-- After processing the first `k` rows, the family spans their common kernel. -/
private theorem spansKernel_kernelBasisUpTo (A : Matrix (Fin r) (Fin n) F) (k : ℕ) :
    SpansKernel {a | ∃ l : Fin r, (l : ℕ) < k ∧ a = A l} (kernelBasisUpTo A k) := by
  induction k with
  | zero =>
    have hset : {a | ∃ l : Fin r, (l : ℕ) < 0 ∧ a = A l} = (∅ : Set (Fin n → F)) :=
      Set.eq_empty_of_forall_notMem fun a ⟨l, hl, _⟩ => Nat.not_lt_zero _ hl
    rw [hset]
    exact spansKernel_single
  | succ k ih =>
    by_cases hk : k < r
    · rw [kernelBasisUpTo, dite_eq_left hk]
      convert ih.kernelStep (A ⟨k, hk⟩) using 1
      ext a
      simp only [Set.mem_ofPred_eq, Set.mem_insert_iff]
      constructor
      · rintro ⟨l, hl, rfl⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hl | hl
        · exact Or.inr ⟨l, hl, rfl⟩
        · exact Or.inl (by rw [show l = ⟨k, hk⟩ from Fin.ext hl])
      · rintro (rfl | ⟨l, hl, rfl⟩)
        · exact ⟨⟨k, hk⟩, Nat.lt_succ_self k, rfl⟩
        · exact ⟨l, Nat.lt_succ_of_lt hl, rfl⟩
    · rw [kernelBasisUpTo, dite_eq_right hk]
      convert ih using 1
      ext a
      simp only [Set.mem_ofPred_eq]
      constructor
      · rintro ⟨l, -, rfl⟩
        exact ⟨l, by omega, rfl⟩
      · rintro ⟨l, hl, rfl⟩
        exact ⟨l, by omega, rfl⟩

/-- The final family spans the kernel of `A`. -/
private theorem spansKernel_kernelBasis (A : Matrix (Fin r) (Fin n) F) :
    SpansKernel (Set.range A) (kernelBasis A) := by
  have hset : {a | ∃ l : Fin r, (l : ℕ) < r ∧ a = A l} = Set.range A :=
    Set.ext fun a => ⟨fun ⟨l, _, hl⟩ => ⟨l, hl.symm⟩, fun ⟨l, hl⟩ => ⟨l, l.2, hl.symm⟩⟩
  have h := spansKernel_kernelBasisUpTo A r
  rw [hset] at h
  exact h

/-- **The kernel vector lies in the kernel.** -/
theorem mulVec_kernelVec (A : Matrix (Fin r) (Fin n) F) : A *ᵥ kernelVec A = 0 := by
  funext k
  simp only [Matrix.mulVec, Pi.zero_apply, kernelVec, dotProduct_sum, dotProduct_smul,
    (spansKernel_kernelBasis A).dotProduct_eq_zero (A k) ⟨k, rfl⟩, smul_zero, sum_const_zero]

/-- **The kernel vector is nonzero when the kernel is nontrivial.** -/
theorem kernelVec_ne_zero (A : Matrix (Fin r) (Fin n) F) (h : ∃ v ≠ 0, A *ᵥ v = 0) :
    kernelVec A ≠ 0 := by
  obtain ⟨v, hv, hAv⟩ := h
  obtain ⟨c, rfl⟩ := (spansKernel_kernelBasis A).exists_eq_sum v (by
    rintro a ⟨k, rfl⟩
    exact congrFun hAv k)
  rcases sum_firstFlags_smul_eq (fun i => if kernelBasis A i = 0 then (0 : F) else 1)
      (kernelBasis A) with ⟨hb, -⟩ | ⟨j, hj, -, hsum⟩
  · refine absurd ?_ hv
    refine sum_eq_zero fun i _ => ?_
    have := congrFun hb i
    simp only [Pi.zero_apply, ite_eq_left_iff, one_ne_zero, imp_false, not_not] at this
    rw [this, smul_zero]
  · unfold kernelVec
    rw [hsum]
    simpa using hj

end Cslib.LinearAlgebra
