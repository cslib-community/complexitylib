/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.Nat.Bitwise.Packing
public import Complexity.Computability.WordRAM.Structured
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Guarded parallel comparison for fusion trees

Each sketch occupies `b` bits, followed by one guard bit. Multiplication replicates the
query into every field, and subtraction compares all fields without borrowing between fields.
This is the packed comparison step of the fusion node in [FredmanWillard1993], following the
authoritative MIT 6.851 Spring 2021 lecture 12 notes, rather than the accompanying scribe notes:
<https://courses.csail.mit.edu/6.851/spring21/lectures/L12.pdf>.

## Main definitions

* `packedNode`: guarded sketches, in little-endian field order.
* `queryMultiplier`: replicates a query by multiplication.
* `packedDifference`: simultaneous guarded subtraction.

## Main results

* `packedDifference_field`: each result field is exactly its guarded scalar difference.
* `packedDifference_guard`: the guard is set exactly when the query is at most the sketch.
* `parallelCompare_exec`: two actual standard-basis instructions produce the raw comparison.

## References

* [M. L. Fredman and D. E. Willard, *Surpassing the information theoretic bound with fusion
  trees*][FredmanWillard1993]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.FusionTree

open scoped BigOperators
open Cslib.BitString

/-- Guarded sketches; field `i` has value `2 ^ b + s i` and width `b + 1`. -/
def packedNode (b n : ℕ) (s : ℕ → ℕ) : ℕ :=
  packRadix (2 ^ (b + 1)) n (fun i => 2 ^ b + s i)

/-- Multiplying by this constant replicates the query into every field. -/
def queryMultiplier (b n : ℕ) : ℕ := packRadix (2 ^ (b + 1)) n (fun _ => 1)

/-- The raw subtraction result; extracting a rank is a separate computation. -/
def packedDifference (b n : ℕ) (s : ℕ → ℕ) (q : ℕ) : ℕ :=
  packedNode b n s - q * queryMultiplier b n

/-- The node's fields start at bit positions `(b + 1) * i`. -/
theorem packedNode_eq_sum (b n : ℕ) (s : ℕ → ℕ) :
    packedNode b n s = ∑ i ∈ Finset.range n, (2 ^ b + s i) * 2 ^ ((b + 1) * i) := by
  simp only [packedNode, packRadix, pow_mul]

/-- Replication is a positional sum, not an extra word-RAM primitive. -/
private theorem query_mul_multiplier (b n q : ℕ) :
    q * queryMultiplier b n = packRadix (2 ^ (b + 1)) n (fun _ => q) := by
  simp [queryMultiplier, packRadix, Finset.mul_sum]

/-- Subtraction is fieldwise: guards prevent any borrow between adjacent sketches. -/
private theorem packedDifference_eq {b n q : ℕ} (s : ℕ → ℕ) (hq : q < 2 ^ b) :
    packedDifference b n s q =
      packRadix (2 ^ (b + 1)) n (fun i => 2 ^ b + s i - q) := by
  have hsum :
      packRadix (2 ^ (b + 1)) n (fun i => 2 ^ b + s i - q) +
        q * queryMultiplier b n = packedNode b n s := by
    rw [query_mul_multiplier]
    simp only [packRadix, packedNode, ← Finset.sum_add_distrib, ← add_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Nat.sub_add_cancel (by omega)]
  unfold packedDifference
  omega

/-- Each field of the simultaneous subtraction is the guarded scalar difference. -/
theorem packedDifference_field {b n q i : ℕ} (s : ℕ → ℕ)
    (hs : ∀ j < n, s j < 2 ^ b) (hq : q < 2 ^ b) (hi : i < n) :
    packedDifference b n s q / 2 ^ ((b + 1) * i) % 2 ^ (b + 1) =
      2 ^ b + s i - q := by
  rw [packedDifference_eq s hq, pow_mul]
  apply packRadix_field (Nat.two_pow_pos _) _ _ hi
  intro j hj
  have := hs j hj
  rw [pow_succ]
  omega

/-- Every bit of a field agrees with the corresponding bit of its scalar difference. -/
private theorem packedDifference_testBit {b n q i j : ℕ} (s : ℕ → ℕ)
    (hs : ∀ k < n, s k < 2 ^ b) (hq : q < 2 ^ b) (hi : i < n) (hj : j < b + 1) :
    (packedDifference b n s q).testBit (j + (b + 1) * i) =
      (2 ^ b + s i - q).testBit j := by
  have h := congrArg (fun x : ℕ => x.testBit j) (packedDifference_field s hs hq hi)
  simpa only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow,
    decide_eq_true hj, Bool.true_and] using h

/-- The guard of field `i` records `q ≤ s i`. Sortedness is unnecessary for this step. -/
theorem packedDifference_guard {b n q i : ℕ} (s : ℕ → ℕ)
    (hs : ∀ j < n, s j < 2 ^ b) (hq : q < 2 ^ b) (hi : i < n) :
    (packedDifference b n s q).testBit (b + (b + 1) * i) = decide (q ≤ s i) := by
  rw [packedDifference_testBit s hs hq hi (by omega), Nat.testBit_eq_decide_div_mod_eq]
  have hs' := hs i hi
  have hp := Nat.two_pow_pos b
  by_cases h : q ≤ s i
  · have hd : (2 ^ b + s i - q) / 2 ^ b = 1 :=
      Nat.div_eq_of_lt_le (by omega) (by omega)
    simp [hd, h]
  · have hd : 2 ^ b + s i - q < 2 ^ b := by omega
    simp [Nat.div_eq_of_lt hd, h]

/-- The precomputed node fits the total field width. -/
theorem packedNode_lt {b n : ℕ} (s : ℕ → ℕ) (hs : ∀ i < n, s i < 2 ^ b) :
    packedNode b n s < 2 ^ ((b + 1) * n) := by
  rw [packedNode, pow_mul]
  apply packRadix_lt
  intro i hi
  have := hs i hi
  rw [pow_succ]
  omega

/-- The multiplier fits even for zero sketches. -/
theorem queryMultiplier_lt (b n : ℕ) : queryMultiplier b n < 2 ^ ((b + 1) * n) := by
  rw [queryMultiplier, pow_mul]
  apply packRadix_lt
  intro i _
  exact Nat.one_lt_two_pow (by omega)

/-- The actual multiplication intermediate fits the total field width. -/
theorem query_mul_multiplier_lt {b n q : ℕ} (hq : q < 2 ^ b) :
    q * queryMultiplier b n < 2 ^ ((b + 1) * n) := by
  rw [query_mul_multiplier, pow_mul]
  apply packRadix_lt
  intro i _
  exact hq.trans_le (Nat.pow_le_pow_right (by decide) (by omega))

/-- The subtraction result fits, so checked overflow needs no modular wraparound. -/
theorem packedDifference_lt {b n q : ℕ} (s : ℕ → ℕ)
    (hs : ∀ i < n, s i < 2 ^ b) :
    packedDifference b n s q < 2 ^ ((b + 1) * n) :=
  (Nat.sub_le _ _).trans_lt (packedNode_lt s hs)

open Cslib.WordRAM

/-- Two fixed standard-basis instructions. Inputs are query in register 0, guarded node in 1,
and multiplier in 2. Register 3 receives the replicated query, and 4 the raw guarded result.
Precomputing/loading the node and multiplier, and converting the result to a rank, are separate.
In particular, this fragment does not assume a unit-cost most-significant-bit operation. -/
def parallelCompareCode : Code .standard 5 :=
  .seq (.op (.bin .mul 3 0 2)) (.op (.bin .sub 4 1 3))

/-- The concrete final data, preserving memory and all three input registers. -/
def parallelCompareResult (x : Data 5) (b n : ℕ) (s : ℕ → ℕ) (q : ℕ) : Data 5 :=
  (x.set 3 (q * queryMultiplier b n)).set 4 (packedDifference b n s q)

/-- All memory is preserved. -/
theorem parallelCompareResult_mem (x : Data 5) (b n : ℕ) (s : ℕ → ℕ) (q : ℕ) :
    (parallelCompareResult x b n s q).mem = x.mem := rfl

/-- The output register's guards are the simultaneous comparison answers. -/
theorem parallelCompareResult_guard {b n q i : ℕ} (s : ℕ → ℕ) (x : Data 5)
    (hs : ∀ j < n, s j < 2 ^ b) (hq : q < 2 ^ b) (hi : i < n) :
    ((parallelCompareResult x b n s q).regs 4).testBit (b + (b + 1) * i) =
      decide (q ≤ s i) := by
  simpa [parallelCompareResult, Data.set] using packedDifference_guard s hs hq hi

/-- Actual checked-overflow execution in exactly two instructions, from arbitrary memory.
The total packed width must fit a word; input delivery is the caller's responsibility. -/
theorem parallelCompare_exec {w b n q : ℕ} (s : ℕ → ℕ) (x : Data 5)
    (hs : ∀ i < n, s i < 2 ^ b) (hq : q < 2 ^ b) (hw : (b + 1) * n ≤ w)
    (hxq : x.regs 0 = q) (hxn : x.regs 1 = packedNode b n s)
    (hxm : x.regs 2 = queryMultiplier b n) :
    Exec w parallelCompareCode x (parallelCompareResult x b n s q) 2 := by
  have hm : Fits w (q * queryMultiplier b n) :=
    (query_mul_multiplier_lt hq).trans_le (Nat.pow_le_pow_right (by decide) hw)
  have hd : Fits w (packedDifference b n s q) :=
    (packedDifference_lt s hs).trans_le (Nat.pow_le_pow_right (by decide) hw)
  have h₁ : Exec w (.op (.bin .mul 3 0 2)) x (x.set 3 (q * queryMultiplier b n)) 1 := by
    simpa only [hxq, hxm, BinOp.eval] using
      (Exec.bin (x := x) (d := 3) (i := 0) (j := 2) (f := .mul) (by
        simpa only [BinOp.eval, hxq, hxm] using hm))
  have h₂ : Exec w (.op (.bin .sub 4 1 3)) (x.set 3 (q * queryMultiplier b n))
      (parallelCompareResult x b n s q) 1 := by
    simpa [parallelCompareResult, packedDifference, hxn, Data.set] using
      (Exec.bin (x := x.set 3 (q * queryMultiplier b n))
        (d := 4) (i := 1) (j := 3) (f := .sub) (by
          simpa [packedDifference, hxn, Data.set] using hd))
  exact .seq h₁ h₂

end Cslib.Algorithms.WordRAM.FusionTree
