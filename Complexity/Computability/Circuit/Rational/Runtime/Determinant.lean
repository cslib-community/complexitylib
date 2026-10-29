/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger, Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Rational.Determinant
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
public import Complexity.Computability.PolyTime.Int.Table
public import Mathlib.Data.Nat.Size
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Foundations.Data.Int.Order
import Mathlib.Data.List.GetD

/-!
# A list program for the staged integer determinant

`Rational.DeterminantAlgorithm.determinant` runs the stages of Bird's division-free determinant on
dense tables whose dimension is part of the type. This file restates the same staged algorithm as
an ordinary program on lists of rows, `Rational.detRows`, whose dimension is the number of rows,
reusing `Cslib.rowEntry` and `Cslib.tabulateTable` from
`Complexity/Computability/PolyTime/Int/Table.lean`, and certifies that it is computable in
polynomial time on multi-tape Turing machines over framed lists of binary sign-magnitude integers
(`Rational.detRows_polytime`). Missing entries read as `0` and extra entries are ignored.

It also bounds the size of every value the program computes. For a `d × d` input whose entries
have absolute value below `2 ^ b`, every entry of the `k`-th stage, and every partial sum and
product computed while producing it, has absolute value below `2 ^ (b + k * (1 + d + b))`.
The bounds are also stated for the bit length `Rational.intBits` of a sign-magnitude binary
encoding, and, following the original development, for the stages of the dense tables.

## Main definitions

* `Rational.rowsOf`, `Rational.ofRows`, `Rational.squareRows`: conversion and square normalization
  between square matrices and lists of rows.
* `Rational.traceTerms`, `Rational.productTerms`, `Rational.stepEntryRows`: the diagonal terms,
  product terms, and entry formula for one Bird stage on lists of rows.
* `Rational.stepRows`, `Rational.stagesRows`: one Bird stage, and the iterated stages.
* `Rational.detRows`: the staged determinant of a list of rows.
* `Rational.intBits`: the bit length of a sign-magnitude binary integer.
* `Rational.stageEntryBound`, `Rational.stageRowBound`, `Rational.stageTableBound`: upper bounds
  on the encoded lengths of entries, rows, and tables in the first `k` Bird stages.

## Main results

* `Rational.intBits_step_le`: bit-length bound on values computed in one stage.
* `Rational.detRows_eq`: `detRows (rowsOf A) = A.det`.
* `Rational.detRows_eq_det_ofRows`: on any list of rows, `detRows` is the determinant of the
  square matrix it denotes, of dimension the number of rows.
* `Rational.natAbs_rowEntry_stagesRows_lt`, `Rational.natAbs_stepEntryRows_lt`,
  `Rational.natAbs_traceTerms_take_sum_lt`, `Rational.natAbs_productTerms_take_sum_lt`: the size
  bounds on stage entries and on the partial sums inside one stage.
* `Rational.intBits_rowEntry_stagesRows_le`: the stage bound in bit length.
* `Rational.DeterminantAlgorithm.stages_power_bound`: the stage bound for dense tables.
* `Rational.length_encList_stagesRows_le`: encoded length bound on intermediate stage tables.
* `Rational.computableInPolyTime_stagesRows`, `Rational.detRows_polytime`: `stagesRows` and
  `detRows` are computable in polynomial time over `encList (encList encIntBin)`.

## References

* The table bounds `step_bound`, `stages_bound` and `stages_power_bound` are adapted from
  OpenAI's formalization [OpenAI2026RationalHitting] at revision
  adc7f1241b42e322a6451854ab7e4b4c146bf78a (file
  lean/OAI/Computability/RationalHitting/Determinant.lean), via the complexitylib port
  [Schlesinger2026RationalHitting] at revision add0aca8ee0d71e68969f2cb45cf91554a50f787.
-/

@[expose] public section

namespace Cslib.Circuits

namespace Rational

/-! ### Bounds on the dense table stages -/

namespace DeterminantAlgorithm

/-- One Bird stage multiplies entry bounds by at most twice the dimension. -/
lemma step_bound {n : ℕ} (A F : Matrix (Fin n) (Fin n) ℤ) (B C : ℕ)
    (hA : ∀ i j, |A i j| ≤ B) (hF : ∀ i j, |F i j| ≤ C) (i j : Fin n) :
    |BirdDet.Spec.stepEntry A F i j| ≤ (2 * n * B * C : ℕ) := by
  have hc : (Finset.Ioi i).card ≤ n :=
    (Finset.card_le_card (Finset.subset_univ _)).trans_eq (by simp)
  have hsum : |∑ k ∈ Finset.Ioi i, F k k| ≤ (n * C : ℕ) := by
    calc _ ≤ ∑ k ∈ Finset.Ioi i, |F k k| := Finset.abs_sum_le_sum_abs _ _
         _ ≤ ∑ _k ∈ Finset.Ioi i, (C : ℤ) := Finset.sum_le_sum fun k _ => hF k k
         _ ≤ (n * C : ℕ) := by
            simp only [Finset.sum_const, nsmul_eq_mul]
            exact_mod_cast Nat.mul_le_mul_right C hc
  have hprod : |∑ k ∈ Finset.Ioi i, F i k * A k j| ≤ (n * C * B : ℕ) := by
    calc _ ≤ ∑ k ∈ Finset.Ioi i, |F i k * A k j| := Finset.abs_sum_le_sum_abs _ _
         _ ≤ ∑ _k ∈ Finset.Ioi i, ((C : ℤ) * (B : ℤ)) := by
            apply Finset.sum_le_sum
            intro k _
            rw [abs_mul]
            exact mul_le_mul (hF i k) (hA k j) (abs_nonneg _) (by positivity)
         _ ≤ (n * C * B : ℕ) := by
            simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_mul]
            exact_mod_cast (Nat.mul_le_mul_right (C * B) hc).trans_eq (Nat.mul_assoc n C B).symm
  rw [BirdDet.Spec.stepEntry_eq]
  calc _ ≤ |(-(∑ k ∈ Finset.Ioi i, F k k)) * A i j| +
          |∑ k ∈ Finset.Ioi i, F i k * A k j| := abs_add_le _ _
       _ ≤ (n * C : ℕ) * (B : ℤ) + (n * C * B : ℕ) := by
          apply add_le_add _ hprod
          rw [abs_mul, abs_neg]
          exact mul_le_mul hsum (hA i j) (abs_nonneg _) (by positivity)
       _ = _ := by push_cast; ring

/-- Every stored table entry has only linearly many multiplicative growth stages. -/
theorem stages_bound {n : ℕ} (A : Table n) (B : ℕ)
    (hA : ∀ i j, |denote A i j| ≤ B) (k : ℕ) (i j : Fin n) :
    |denote (stages A k) i j| ≤ (B * (2 * n * B) ^ k : ℕ) := by
  induction k generalizing i j with
  | zero => simpa [stages] using hA i j
  | succ k ih =>
    simp only [stages, step, denote_tabulate]
    convert step_bound (denote A) (denote (stages A k)) B (B * (2 * n * B) ^ k) hA
      (fun u v => ih u v) i j using 1
    push_cast
    ring

/-- Binary exponent bound for all stored intermediate tables, including singular inputs. -/
theorem stages_power_bound {n : ℕ} (A : Table n) (b : ℕ)
    (hA : ∀ i j, |denote A i j| ≤ (2 : ℤ) ^ b) (k : ℕ) (i j : Fin n) :
    |denote (stages A k) i j| ≤ (2 : ℤ) ^ (b + k * (1 + n + b)) := by
  have hf : 2 * n * 2 ^ b ≤ 2 ^ (1 + n + b) := by
    calc _ ≤ 2 * 2 ^ n * 2 ^ b :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ Nat.lt_two_pow_self.le)
         _ = _ := by rw [pow_add, pow_add]; norm_num
  calc _ ≤ ((2 ^ b * (2 * n * 2 ^ b) ^ k : ℕ) : ℤ) :=
          stages_bound A (2 ^ b) (by simpa using hA) k i j
       _ ≤ ((2 ^ b * (2 ^ (1 + n + b)) ^ k : ℕ) : ℤ) := by
          exact_mod_cast Nat.mul_le_mul_left (2 ^ b) (Nat.pow_le_pow_left hf k)
       _ = (2 : ℤ) ^ (b + k * (1 + n + b)) := by
          simp only [Nat.cast_pow, Nat.cast_ofNat, ← pow_mul, ← pow_add, Nat.mul_comm]

end DeterminantAlgorithm

/-! ### The list program -/

export Cslib (rowEntry tabulateTable exists_rowEntry_eq
  computableInPolyTime_rowEntry computableInPolyTime_tabulateTable)

/-- The list of rows of a square matrix. -/
def rowsOf {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ) : List (List ℤ) :=
  (List.finRange d).map fun i => (List.finRange d).map (A i)

/-- The square matrix denoted by a list of rows: its dimension is the number of rows, missing
entries are `0` and extra entries are ignored. -/
def ofRows (rows : List (List ℤ)) : Matrix (Fin rows.length) (Fin rows.length) ℤ :=
  Matrix.of fun i j => rowEntry rows i j

/-- Pad or truncate every row to the number of rows. -/
def squareRows (rows : List (List ℤ)) : List (List ℤ) :=
  tabulateTable rows.length rows.length (rowEntry rows)

/-- The diagonal entries `F k k` for `i < k < d`, summed in one Bird stage; `d` is the number of
rows of `A`. -/
def traceTerms (A F : List (List ℤ)) (i : ℕ) : List ℤ :=
  ((List.range A.length).drop (i + 1)).map fun k => rowEntry F k k

/-- The products `F i k * A k j` for `i < k < d`, summed in one Bird stage; `d` is the number of
rows of `A`. -/
def productTerms (A F : List (List ℤ)) (i j : ℕ) : List ℤ :=
  ((List.range A.length).drop (i + 1)).map fun k => rowEntry F i k * rowEntry A k j

/-- Entry `(i, j)` of one Bird stage, `BirdDet.Spec.stepEntry`, on lists of rows. -/
def stepEntryRows (A F : List (List ℤ)) (i j : ℕ) : ℤ :=
  -(traceTerms A F i).sum * rowEntry A i j + (productTerms A F i j).sum

/-- One Bird stage on lists of rows. -/
def stepRows (A F : List (List ℤ)) : List (List ℤ) :=
  tabulateTable A.length A.length (stepEntryRows A F)

/-- The `k`-th Bird stage, starting from the squared input. -/
def stagesRows (A : List (List ℤ)) (k : ℕ) : List (List ℤ) :=
  (stepRows A)^[k] (squareRows A)

/-- The staged division-free determinant of a list of rows, including dimension zero. -/
def detRows (A : List (List ℤ)) : ℤ :=
  match A.length with
  | 0 => 1
  | k + 1 => (-1) ^ k * rowEntry (stagesRows A k) 0 0

/-- The bit length of an integer in a sign-magnitude binary encoding: one sign bit followed by
the binary digits of the absolute value. -/
def intBits (z : ℤ) : ℕ :=
  Nat.size z.natAbs + 1

/-- `intBits z` is the length of the binary sign-magnitude code of `z`. -/
theorem intBits_eq_length_encIntBin (z : ℤ) :
    intBits z = (Turing.MultiTapeTM.encIntBin z).length := by
  rw [Turing.MultiTapeTM.length_encIntBin]
  rfl

/-! ### Basic lemmas -/

/-- The list of rows `rowsOf A` of a `d × d` matrix `A` has length `d`. -/
@[simp] lemma length_rowsOf {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ) : (rowsOf A).length = d := by
  simp [rowsOf]

/-- Looking up entry `(i, j)` in `rowsOf A` recovers `A i j`. -/
lemma rowEntry_rowsOf {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ) (i j : Fin d) :
    rowEntry (rowsOf A) i j = A i j := by
  simp [rowEntry, rowsOf, List.getD_eq_getElem?_getD]

private lemma stagesRows_zero (A : List (List ℤ)) : stagesRows A 0 = squareRows A := rfl

private lemma stagesRows_succ (A : List (List ℤ)) (k : ℕ) :
    stagesRows A (k + 1) = stepRows A (stagesRows A k) :=
  Function.iterate_succ_apply' _ _ _

/-- A tail of a range, summed as a list, is a tail sum over `Fin`. -/
private lemma sum_map_drop_range (d lo : ℕ) (f : ℕ → ℤ) :
    (((List.range d).drop lo).map f).sum = BirdDet.sumFrom d lo f := by
  induction lo using BirdDet.sumFrom_induct d with
  | step lo hlo ih =>
    rw [BirdDet.sumFrom_step d lo f hlo, ← ih,
      List.drop_eq_getElem_cons (by simpa using hlo)]
    simp
  | stop lo hlo =>
    rw [BirdDet.sumFrom_stop d lo f hlo, List.drop_eq_nil_of_le (by simpa using hlo)]
    rfl

lemma sum_map_drop_range_fin {d : ℕ} (i : Fin d) (f : ℕ → ℤ) :
    (((List.range d).drop (i.val + 1)).map f).sum = ∑ k ∈ Finset.Ioi i, f k.val := by
  rw [sum_map_drop_range, DeterminantAlgorithm.sumFrom_fin_tail]

/-! ### Correctness -/

/-- The list stages agree with the Bird stages of the matrix denoted by the input. -/
private theorem rowEntry_stagesRows (A : List (List ℤ)) (k : ℕ) (i j : Fin A.length) :
    rowEntry (stagesRows A k) i j =
      ((BirdDet.Spec.stepEntry (ofRows A))^[k] (ofRows A)) i j := by
  induction k generalizing i j with
  | zero =>
    rw [stagesRows_zero, squareRows, rowEntry_tabulateTable, ite_eq_left ⟨i.isLt, j.isLt⟩]
    rfl
  | succ k ih =>
    rw [stagesRows_succ, Function.iterate_succ_apply', stepRows, rowEntry_tabulateTable,
      ite_eq_left ⟨i.isLt, j.isLt⟩, stepEntryRows, traceTerms, productTerms,
      sum_map_drop_range_fin, sum_map_drop_range_fin, BirdDet.Spec.stepEntry_eq]
    simp only [ih, Matrix.of_apply, ofRows]

private lemma birdDet_eq_of_eq_zero {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (hn : n = 0) :
    BirdDet.Spec.birdDet M = 1 := by
  subst hn
  exact BirdDet.Spec.birdDetSpec_zero M

private lemma birdDet_eq_of_eq_succ {n k : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (hn : n = k + 1) :
    BirdDet.Spec.birdDet M =
      (-1) ^ k * ((BirdDet.Spec.stepEntry M)^[k] M) ⟨0, by omega⟩ ⟨0, by omega⟩ := by
  subst hn
  exact BirdDet.Spec.birdDetSpec_succ M

/-- On any list of rows, `detRows` is the determinant of the square matrix it denotes, of
dimension the number of rows. -/
theorem detRows_eq_det_ofRows (A : List (List ℤ)) : detRows A = (ofRows A).det := by
  rw [← DeterminantAlgorithm.spec_eq_det]
  unfold detRows
  split
  · next h => exact (birdDet_eq_of_eq_zero _ h).symm
  · next k h =>
    rw [birdDet_eq_of_eq_succ _ h]
    exact congrArg _ (rowEntry_stagesRows A k ⟨0, by omega⟩ ⟨0, by omega⟩)

/-- `detRows` computes the determinant of every list of rows that agrees with a square matrix
of its length. -/
theorem detRows_eq_det_of_rowEntry {d : ℕ} {rows : List (List ℤ)}
    (A : Matrix (Fin d) (Fin d) ℤ) (hd : rows.length = d)
    (hA : ∀ i j : Fin d, rowEntry rows i j = A i j) : detRows rows = A.det := by
  subst hd
  rw [detRows_eq_det_ofRows]
  congr 1
  ext i j
  exact hA i j

/-- The list program computes the determinant. -/
theorem detRows_eq {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ) : detRows (rowsOf A) = A.det :=
  detRows_eq_det_of_rowEntry A (length_rowsOf A) (rowEntry_rowsOf A)

/-- The list program agrees with the staged determinant on dense tables. -/
theorem detRows_rowsOf_denote {d : ℕ} (A : DeterminantAlgorithm.Table d) :
    detRows (rowsOf (DeterminantAlgorithm.denote A)) = DeterminantAlgorithm.determinant A := by
  rw [detRows_eq, DeterminantAlgorithm.determinant_eq]

/-! ### Size bounds -/

/-- Entry bounds hold for every entry index once they hold for every stored entry. -/
lemma natAbs_rowEntry_lt {rows : List (List ℤ)} {b : ℕ}
    (h : ∀ row ∈ rows, ∀ z ∈ row, z.natAbs < 2 ^ b) (i j : ℕ) :
    (rowEntry rows i j).natAbs < 2 ^ b :=
  rowEntry_rel_of_mem (Nat.two_pow_pos b) h i j

private lemma length_traceTerms_le (A F : List (List ℤ)) (i : ℕ) :
    (traceTerms A F i).length ≤ A.length := by
  simp only [traceTerms, List.length_map, List.length_drop, List.length_range]
  omega

private lemma length_productTerms_le (A F : List (List ℤ)) (i j : ℕ) :
    (productTerms A F i j).length ≤ A.length := by
  simp only [productTerms, List.length_map, List.length_drop, List.length_range]
  omega

section StepBounds

variable {A F : List (List ℤ)} {b e : ℕ}

/-- The common bound on all values computed in one stage, before the final addition. -/
private lemma length_mul_lt (A : List (List ℤ)) (b e : ℕ) :
    A.length * (2 ^ e * 2 ^ b) < 2 ^ (e + b + A.length) := by
  rw [pow_add (2 : ℕ) (e + b), pow_add, Nat.mul_comm]
  exact Nat.mul_lt_mul_of_pos_left Nat.lt_two_pow_self (by positivity)

private lemma half_le_bound (A : List (List ℤ)) (b e : ℕ) :
    2 ^ (e + b + A.length) ≤ 2 ^ (e + (1 + A.length + b)) :=
  Nat.pow_le_pow_right (by norm_num) (by omega)

private lemma traceTerms_take_le (hF : ∀ i j, (rowEntry F i j).natAbs < 2 ^ e) (i m : ℕ) :
    ((traceTerms A F i).take m).sum.natAbs ≤ A.length * (2 ^ e * 2 ^ b) := by
  refine (List.natAbs_sum_take_le_length_mul (C := 2 ^ e) ?_ m).trans ?_
  · intro x hx
    obtain ⟨k, -, rfl⟩ := List.mem_map.mp hx
    exact (hF k k).le
  · exact Nat.mul_le_mul (length_traceTerms_le A F i) (Nat.le_mul_of_pos_right _ (by positivity))

private lemma productTerms_take_le (hA : ∀ i j, (rowEntry A i j).natAbs < 2 ^ b)
    (hF : ∀ i j, (rowEntry F i j).natAbs < 2 ^ e) (i j m : ℕ) :
    ((productTerms A F i j).take m).sum.natAbs ≤ A.length * (2 ^ e * 2 ^ b) := by
  refine (List.natAbs_sum_take_le_length_mul (C := 2 ^ e * 2 ^ b) ?_ m).trans
    (Nat.mul_le_mul_right _ (length_productTerms_le A F i j))
  intro x hx
  obtain ⟨k, -, rfl⟩ := List.mem_map.mp hx
  rw [Int.natAbs_mul]
  exact Nat.mul_le_mul (hF i k).le (hA k j).le

/-- Every prefix sum of the diagonal terms of one stage obeys the next stage's bound. -/
theorem natAbs_traceTerms_take_sum_lt (hF : ∀ i j, (rowEntry F i j).natAbs < 2 ^ e) (i m : ℕ) :
    ((traceTerms A F i).take m).sum.natAbs < 2 ^ (e + (1 + A.length + b)) :=
  ((traceTerms_take_le (b := b) hF i m).trans_lt (length_mul_lt A b e)).trans_le
    (half_le_bound A b e)

/-- Every prefix sum of the product terms of one stage obeys the next stage's bound. -/
theorem natAbs_productTerms_take_sum_lt (hA : ∀ i j, (rowEntry A i j).natAbs < 2 ^ b)
    (hF : ∀ i j, (rowEntry F i j).natAbs < 2 ^ e) (i j m : ℕ) :
    ((productTerms A F i j).take m).sum.natAbs < 2 ^ (e + (1 + A.length + b)) :=
  ((productTerms_take_le hA hF i j m).trans_lt (length_mul_lt A b e)).trans_le
    (half_le_bound A b e)

private lemma trace_mul_le (hA : ∀ i j, (rowEntry A i j).natAbs < 2 ^ b)
    (hF : ∀ i j, (rowEntry F i j).natAbs < 2 ^ e) (i j : ℕ) :
    ((traceTerms A F i).sum * rowEntry A i j).natAbs ≤ A.length * (2 ^ e * 2 ^ b) := by
  have h := List.natAbs_sum_take_le_length_mul (l := traceTerms A F i) (C := 2 ^ e)
    (fun x hx => by
      obtain ⟨k, -, rfl⟩ := List.mem_map.mp hx
      exact (hF k k).le) (traceTerms A F i).length
  rw [List.take_length] at h
  rw [Int.natAbs_mul, ← Nat.mul_assoc]
  exact Nat.mul_le_mul (h.trans (Nat.mul_le_mul_right _ (length_traceTerms_le A F i)))
    (hA i j).le

/-- The trace product computed in one stage obeys the next stage's bound. -/
private theorem natAbs_traceTerms_sum_mul_lt (hA : ∀ i j, (rowEntry A i j).natAbs < 2 ^ b)
    (hF : ∀ i j, (rowEntry F i j).natAbs < 2 ^ e) (i j : ℕ) :
    ((traceTerms A F i).sum * rowEntry A i j).natAbs < 2 ^ (e + (1 + A.length + b)) :=
  ((trace_mul_le hA hF i j).trans_lt (length_mul_lt A b e)).trans_le (half_le_bound A b e)

/-- One stage multiplies the entry bound by at most `2 ^ (1 + d + b)`. -/
theorem natAbs_stepEntryRows_lt (hA : ∀ i j, (rowEntry A i j).natAbs < 2 ^ b)
    (hF : ∀ i j, (rowEntry F i j).natAbs < 2 ^ e) (i j : ℕ) :
    (stepEntryRows A F i j).natAbs < 2 ^ (e + (1 + A.length + b)) := by
  have h₁ := (trace_mul_le hA hF i j).trans_lt (length_mul_lt A b e)
  have h₂ := ((productTerms_take_le hA hF i j (productTerms A F i j).length).trans_lt
    (length_mul_lt A b e))
  rw [List.take_length] at h₂
  have h₃ : 2 ^ (e + (1 + A.length + b)) = 2 ^ (e + b + A.length) + 2 ^ (e + b + A.length) := by
    rw [← Nat.two_mul, ← Nat.pow_succ']
    congr 1
    omega
  rw [stepEntryRows, h₃, neg_mul]
  calc (-((traceTerms A F i).sum * rowEntry A i j) + (productTerms A F i j).sum).natAbs
      ≤ (-((traceTerms A F i).sum * rowEntry A i j)).natAbs + (productTerms A F i j).sum.natAbs :=
        Int.natAbs_add_le _ _
    _ < _ := by
        rw [Int.natAbs_neg]
        exact Nat.add_lt_add h₁ h₂

end StepBounds

/-- Every entry of the `k`-th stage of an input with entries below `2 ^ b` in absolute value is
below `2 ^ (b + k * (1 + d + b))`, where `d` is the number of rows. -/
theorem natAbs_rowEntry_stagesRows_lt {A : List (List ℤ)} {b : ℕ}
    (hA : ∀ i j, (rowEntry A i j).natAbs < 2 ^ b) (k i j : ℕ) :
    (rowEntry (stagesRows A k) i j).natAbs < 2 ^ (b + k * (1 + A.length + b)) := by
  induction k generalizing i j with
  | zero =>
    rw [stagesRows_zero, squareRows, rowEntry_tabulateTable, Nat.zero_mul, Nat.add_zero]
    split_ifs
    · exact hA i j
    · exact Nat.two_pow_pos b
  | succ k ih =>
    rw [stagesRows_succ, stepRows, rowEntry_tabulateTable,
      show b + (k + 1) * (1 + A.length + b) = b + k * (1 + A.length + b) + (1 + A.length + b) by
        ring]
    split_ifs
    · exact natAbs_stepEntryRows_lt hA ih i j
    · exact Nat.two_pow_pos _

/-- The stage bound for every stored entry of a stage. -/
theorem natAbs_lt_of_mem_stagesRows {A : List (List ℤ)} {b : ℕ}
    (hA : ∀ i j, (rowEntry A i j).natAbs < 2 ^ b) (k : ℕ) {row : List ℤ}
    (hrow : row ∈ stagesRows A k) {z : ℤ} (hz : z ∈ row) :
    z.natAbs < 2 ^ (b + k * (1 + A.length + b)) := by
  obtain ⟨i, j, rfl⟩ := exists_rowEntry_eq hrow hz
  exact natAbs_rowEntry_stagesRows_lt hA k i j

/-! ### Bounds in bit length -/

/-- An integer `z` has sign-magnitude bit length `intBits z ≤ e + 1` if and only if
`z.natAbs < 2 ^ e`. -/
lemma intBits_le_iff (z : ℤ) (e : ℕ) : intBits z ≤ e + 1 ↔ z.natAbs < 2 ^ e := by
  rw [intBits, Nat.add_le_add_iff_right, Nat.size_le]

/-- Every integer has sign-magnitude bit length at least `1`. -/
lemma one_le_intBits (z : ℤ) : 1 ≤ intBits z :=
  Nat.le_add_left 1 _

/-- The stage bound in bit length: inputs of at most `b + 1` bits give `k`-th stage entries of
at most `b + k * (1 + d + b) + 1` bits. -/
theorem intBits_rowEntry_stagesRows_le {A : List (List ℤ)} {b : ℕ}
    (hA : ∀ i j, intBits (rowEntry A i j) ≤ b + 1) (k i j : ℕ) :
    intBits (rowEntry (stagesRows A k) i j) ≤ b + k * (1 + A.length + b) + 1 :=
  (intBits_le_iff _ _).mpr
    (natAbs_rowEntry_stagesRows_lt (fun i j => (intBits_le_iff _ _).mp (hA i j)) k i j)

/-- The bit-length stage bound for every stored entry of a stage. -/
theorem intBits_le_of_mem_stagesRows {A : List (List ℤ)} {b : ℕ}
    (hA : ∀ row ∈ A, ∀ z ∈ row, intBits z ≤ b + 1) (k : ℕ) {row : List ℤ}
    (hrow : row ∈ stagesRows A k) {z : ℤ} (hz : z ∈ row) :
    intBits z ≤ b + k * (1 + A.length + b) + 1 :=
  (intBits_le_iff _ _).mpr <| natAbs_lt_of_mem_stagesRows
    (natAbs_rowEntry_lt fun row hrow z hz => (intBits_le_iff _ _).mp (hA row hrow z hz)) k hrow hz

/-- The bit-length bound on every value computed in one stage: prefix sums of both term lists,
the trace product and the new entry. -/
theorem intBits_step_le {A F : List (List ℤ)} {b e : ℕ}
    (hA : ∀ i j, intBits (rowEntry A i j) ≤ b + 1)
    (hF : ∀ i j, intBits (rowEntry F i j) ≤ e + 1) (i j m : ℕ) :
    intBits ((traceTerms A F i).take m).sum ≤ e + (1 + A.length + b) + 1 ∧
      intBits ((productTerms A F i j).take m).sum ≤ e + (1 + A.length + b) + 1 ∧
      intBits ((traceTerms A F i).sum * rowEntry A i j) ≤ e + (1 + A.length + b) + 1 ∧
      intBits (stepEntryRows A F i j) ≤ e + (1 + A.length + b) + 1 := by
  have hA' i j := (intBits_le_iff _ _).mp (hA i j)
  have hF' i j := (intBits_le_iff _ _).mp (hF i j)
  simp only [intBits_le_iff]
  exact ⟨natAbs_traceTerms_take_sum_lt hF' i m, natAbs_productTerms_take_sum_lt hA' hF' i j m,
    natAbs_traceTerms_sum_mul_lt hA' hF' i j, natAbs_stepEntryRows_lt hA' hF' i j⟩

/-! ### Polynomial-time certificate -/

open Turing MultiTapeTM MultiTapeTM.ComputableInPolyTime

/-- Every stage table `stagesRows A k` has `A.length` rows. -/
@[simp] lemma length_stagesRows (A : List (List ℤ)) (k : ℕ) :
    (stagesRows A k).length = A.length := by
  cases k <;> simp [stagesRows_zero, stagesRows_succ, squareRows, stepRows, length_tabulateTable]

/-- Every row in `stagesRows A k` has length `A.length`. -/
lemma length_of_mem_stagesRows {A : List (List ℤ)} {k : ℕ} {row : List ℤ}
    (hrow : row ∈ stagesRows A k) : row.length = A.length := by
  cases k with
  | zero => exact length_of_mem_tabulateTable hrow
  | succ k => rw [stagesRows_succ] at hrow; exact length_of_mem_tabulateTable hrow

private lemma intBits_le_length_encList {A : List (List ℤ)} {row : List ℤ} (hrow : row ∈ A)
    {z : ℤ} (hz : z ∈ row) : intBits z ≤ (encList (encList encIntBin) A).length + 1 := by
  rw [intBits_eq_length_encIntBin]
  exact ((length_le_encList_of_mem encIntBin hz).trans
    (length_le_encList_of_mem (encList encIntBin) hrow)).trans (Nat.le_succ _)

/-- Upper bound on the bit length of any entry in the first `k` Bird stages of a matrix of encoded
length `L`. -/
def stageEntryBound (L k : ℕ) : ℕ := L + k * (2 * L + 1) + 1

/-- Upper bound on the encoded length of any row in the first `k` Bird stages of a matrix of
encoded length `L`. -/
def stageRowBound (L k : ℕ) : ℕ := L * (2 * stageEntryBound L k + 1)

/-- Upper bound on the encoded length of any stage table in the first `k` Bird stages of a matrix
of encoded length `L`. -/
def stageTableBound (L k : ℕ) : ℕ := L * (2 * stageRowBound L k + 1)

/-- Every stage table up to stage `k` has encoded length bounded by `stageTableBound`. -/
theorem length_encList_stagesRows_le (A : List (List ℤ)) {i k : ℕ} (hik : i ≤ k) :
    (encList (encList encIntBin) (stagesRows A i)).length ≤
      stageTableBound (encList (encList encIntBin) A).length k := by
  set L := (encList (encList encIntBin) A).length
  have hlen : A.length ≤ L := length_le_length_encList (encList encIntBin) A
  have hentry {row : List ℤ} (hrow : row ∈ stagesRows A i) {z : ℤ} (hz : z ∈ row) :
      (encIntBin z).length ≤ stageEntryBound L k := by
    rw [← intBits_eq_length_encIntBin]
    exact (intBits_le_of_mem_stagesRows (fun _ hr _ hz' => intBits_le_length_encList hr hz')
      i hrow hz).trans
      (Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul hik (by omega)) L) 1)
  have hrow_le {row : List ℤ} (hrow : row ∈ stagesRows A i) :
      (encList encIntBin row).length ≤ stageRowBound L k := by
    refine (length_encList_le encIntBin row fun z hz => hentry hrow hz).trans ?_
    rw [length_of_mem_stagesRows hrow]
    exact Nat.mul_le_mul_right _ hlen
  refine (length_encList_le (encList encIntBin) (stagesRows A i)
    fun row hrow => hrow_le hrow).trans ?_
  rw [length_stagesRows]
  exact Nat.mul_le_mul_right _ hlen

private lemma polyBounded_stageTableBound {α : Type} {size L k : α → ℕ}
    (hL : PolyBounded size L) (hk : PolyBounded size k) :
    PolyBounded size (fun x => stageTableBound (L x) (k x)) := by
  have hentry : PolyBounded size (fun x => stageEntryBound (L x) (k x)) :=
    (hL.add (hk.mul (((PolyBounded.const 2).mul hL).add (.const 1)))).add (.const 1)
  have hrow : PolyBounded size (fun x => stageRowBound (L x) (k x)) :=
    hL.mul (((PolyBounded.const 2).mul hentry).add (.const 1))
  exact hL.mul (((PolyBounded.const 2).mul hrow).add (.const 1))

variable {α : Type} {encIn : α ↪ List Bool}

/-- Padding or truncating a list of rows to a square table is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_squareRows :
    ComputableInPolyTime squareRows
      (encList (encList encIntBin)) (encList (encList encIntBin)) :=
  computableInPolyTime_tabulateTable (length_list _) (length_list _) (by fun_prop)

@[local fun_prop]
private theorem dropUnary_list {β : Type} {encB : β ↪ List Bool} {l : α → List β} {n : α → ℕ}
    (hl : ComputableInPolyTime l encIn (encList encB))
    (hn : ComputableInPolyTime n encIn encUnary) :
    ComputableInPolyTime (fun x => (l x).drop (n x)) encIn (encList encB) :=
  (dropUnary (encA := encB)).comp (hl.prod hn)

/-- Computing the diagonal terms summed in one Bird stage is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_traceTerms {A F : α → List (List ℤ)} {i : α → ℕ}
    (hA : ComputableInPolyTime A encIn (encList (encList encIntBin)))
    (hF : ComputableInPolyTime F encIn (encList (encList encIntBin)))
    (hi : ComputableInPolyTime i encIn encUnary) :
    ComputableInPolyTime (fun x => traceTerms (A x) (F x) (i x))
      encIn (encList encIntBin) := by
  unfold traceTerms; fun_prop

/-- Computing the product terms summed in one Bird stage is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_productTerms {A F : α → List (List ℤ)} {i j : α → ℕ}
    (hA : ComputableInPolyTime A encIn (encList (encList encIntBin)))
    (hF : ComputableInPolyTime F encIn (encList (encList encIntBin)))
    (hi : ComputableInPolyTime i encIn encUnary)
    (hj : ComputableInPolyTime j encIn encUnary) :
    ComputableInPolyTime (fun x => productTerms (A x) (F x) (i x) (j x))
      encIn (encList encIntBin) := by
  unfold productTerms; fun_prop

/-- Computing one entry of a Bird stage is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_stepEntryRows {A F : α → List (List ℤ)} {i j : α → ℕ}
    (hA : ComputableInPolyTime A encIn (encList (encList encIntBin)))
    (hF : ComputableInPolyTime F encIn (encList (encList encIntBin)))
    (hi : ComputableInPolyTime i encIn encUnary)
    (hj : ComputableInPolyTime j encIn encUnary) :
    ComputableInPolyTime (fun x => stepEntryRows (A x) (F x) (i x) (j x))
      encIn encIntBin := by
  unfold stepEntryRows; fun_prop

/-- One Bird stage on lists of rows is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_stepRows :
    ComputableInPolyTime (fun p : List (List ℤ) × List (List ℤ) => stepRows p.1 p.2)
      (encPair (encList (encList encIntBin)) (encList (encList encIntBin)))
      (encList (encList encIntBin)) :=
  computableInPolyTime_tabulateTable (by fun_prop) (by fun_prop) (by fun_prop)

/-- Iterating `k` Bird stages on a list of rows is polynomial-time for a unary stage count `k`. -/
@[fun_prop]
theorem computableInPolyTime_stagesRows {A : α → List (List ℤ)} {k : α → ℕ}
    (hA : ComputableInPolyTime A encIn (encList (encList encIntBin)))
    (hk : ComputableInPolyTime k encIn encUnary) :
    ComputableInPolyTime (fun x => stagesRows (A x) (k x))
      encIn (encList (encList encIntBin)) :=
  iterateWith hA hk (computableInPolyTime_squareRows.comp hA)
    computableInPolyTime_stepRows
    (polyBounded_stageTableBound hA.polyBounded_length hk.polyBounded)
    fun x _ hi => length_encList_stagesRows_le (A x) hi

private lemma detRows_eq_ite (A : List (List ℤ)) :
    detRows A =
      if A.isEmpty then 1
      else (-1) ^ (A.length - 1) * rowEntry (stagesRows A (A.length - 1)) 0 0 := by
  unfold detRows
  cases h : A.length with
  | zero => rw [List.length_eq_zero_iff.mp h]; rfl
  | succ k =>
    have hne : A.isEmpty = false := by
      rw [Bool.eq_false_iff, ne_eq, List.isEmpty_iff]; intro hA; simp [hA] at h
    simp [hne]

/-- The staged division-free integer determinant `detRows` is computable in polynomial
time on lists of rows of binary sign-magnitude integers. -/
@[fun_prop]
theorem detRows_polytime :
    ComputableInPolyTime detRows (encList (encList encIntBin)) encIntBin := by
  have h : ComputableInPolyTime
      (fun A : List (List ℤ) =>
        if A.isEmpty then 1
        else (-1) ^ (A.length - 1) * rowEntry (stagesRows A (A.length - 1)) 0 0)
      (encList (encList encIntBin)) encIntBin := by fun_prop
  simpa only [← detRows_eq_ite] using h

end Rational

end Cslib.Circuits
