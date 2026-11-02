/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime.Header
import Mathlib.Data.List.GetD
import Mathlib.Tactic.IntervalCases

/-!
# Original-word sum and copied-input meaning

The runtime copy loop computes the sum of exactly the three original matrix spans. That sum
bounds every signed input magnitude and is polynomial under the original weight hypothesis.
It is not supplied as a certificate or computed by an uncharged preprocessing operation.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime

open Cslib.WordRAM

/-- Sum accumulated by the three native matrix copies, in original row-major order. -/
@[expose] def rawTotal (n : ℕ) (values : List ℤ) : ℕ :=
  ∑ q ∈ Finset.range (3 * (n * n)), Signed.encode (values.getD q 0)

/-- No additional scan of the matrices is needed: the three copy accumulators concatenate. -/
theorem rawTotal_split (n : ℕ) (values : List ℤ) :
    rawTotal n values =
      (∑ q ∈ Finset.range (n * n), Signed.encode (values.getD q 0)) +
      (∑ q ∈ Finset.range (n * n), Signed.encode (values.getD (n * n + q) 0)) +
      (∑ q ∈ Finset.range (n * n), Signed.encode (values.getD (2 * (n * n) + q) 0)) := by
  unfold rawTotal
  rw [show 3 * (n * n) = (n * n + n * n) + n * n by omega,
    Finset.sum_range_add, Finset.sum_range_add]
  simp only [two_mul]

/-- Every original integer fits the magnitude supplied by the actual word accumulator. -/
theorem natAbs_le_rawTotal {n : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (z : ℤ) (hz : z ∈ values) :
    z.natAbs ≤ rawTotal n values := by
  obtain ⟨q, hq, he⟩ := List.mem_iff_getElem.mp hz
  have henc : z.natAbs ≤ Signed.encode z := by unfold Signed.encode; omega
  apply henc.trans
  have hs : Signed.encode (values.getD q 0) ≤ rawTotal n values := by
    unfold rawTotal
    exact Finset.single_le_sum (f := fun q : ℕ => Signed.encode (values.getD q 0))
      (fun _ _ => Nat.zero_le _)
      (show q ∈ Finset.range (3 * (n * n)) from Finset.mem_range.mpr (by omega))
  simpa only [List.getD_eq_getElem _ _ hq, he] using hs

/-- Original polynomial weight bounds also bound the computed runtime word sum. -/
theorem rawTotal_le {n A : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hv : ∀ z ∈ values, z.natAbs ≤ A) :
    rawTotal n values ≤ 3 * (n * n) * (2 * A + 1) := by
  calc
    _ ≤ ∑ _q ∈ Finset.range (3 * (n * n)), (2 * A + 1) := by
      apply Finset.sum_le_sum
      intro q hq
      have hql : q < values.length := by have := Finset.mem_range.mp hq; omega
      have hmem : values.getD q 0 ∈ values := by
        rw [List.getD_eq_getElem _ _ hql]
        exact List.getElem_mem _
      have hb := hv _ hmem
      unfold Signed.encode
      split_ifs <;> omega
    _ = _ := by simp

/-- Scalar stores do not change the caller prefix. -/
theorem headerMemory_below (mem : ℕ → ℕ) (b n D g p q : ℕ) (hq : q < b) :
    headerMemory mem b n D g p q = mem q := by
  simp only [headerMemory, Function.update_of_ne (by omega : q ≠ b + 4),
    Function.update_of_ne (by omega : q ≠ b + 3),
    Function.update_of_ne (by omega : q ≠ b + 2),
    Function.update_of_ne (by omega : q ≠ b + 1),
    Function.update_of_ne (by omega : q ≠ b)]

/-- The scalar header writes exactly five cells. -/
theorem headerMemory_outside (mem : ℕ → ℕ) (b n D g p q : ℕ)
    (hq : q < b ∨ b + 5 ≤ q) : headerMemory mem b n D g p q = mem q := by
  simp only [headerMemory, Function.update_of_ne (by omega : q ≠ b + 4),
    Function.update_of_ne (by omega : q ≠ b + 3),
    Function.update_of_ne (by omega : q ≠ b + 2),
    Function.update_of_ne (by omega : q ≠ b + 1),
    Function.update_of_ne (by omega : q ≠ b)]

/-- Memory after the actual five header stores and three square copies. -/
@[expose] def copyMemory (mem : ℕ → ℕ) (b n D g p ab bc ac : ℕ) : ℕ → ℕ :=
  ArrayCopy.copyPrefix (ArrayCopy.copyPrefix (ArrayCopy.copyPrefix
    (headerMemory mem b n D g p) ab (b + 5) (n * n))
      bc (b + 5 + n * n) (n * n)) ac (b + 5 + n * n + n * n) (n * n)

/-- The actual copied spans never change the original caller prefix. -/
theorem copyMemory_below (mem : ℕ → ℕ) (b n D g p ab bc ac q : ℕ) (hq : q < b) :
    copyMemory mem b n D g p ab bc ac q = mem q := by
  unfold copyMemory
  rw [ArrayCopy.copyPrefix_outside (by omega), ArrayCopy.copyPrefix_outside (by omega),
    ArrayCopy.copyPrefix_outside (by omega), headerMemory_below _ _ _ _ _ _ _ hq]

/-- Input adaptation touches only its five header words and three original squares. -/
theorem copyMemory_outside (mem : ℕ → ℕ) (b n D g p ab bc ac q : ℕ)
    (hq : q < b ∨ b + 5 + 3 * (n * n) ≤ q) :
    copyMemory mem b n D g p ab bc ac q = mem q := by
  unfold copyMemory
  rw [ArrayCopy.copyPrefix_outside (by omega), ArrayCopy.copyPrefix_outside (by omega),
    ArrayCopy.copyPrefix_outside (by omega), headerMemory_outside _ _ _ _ _ _ _ (by omega)]

/-- The three real copies preserve canonical signed encoding and original matrix order.
Their source arrays may alias one another; every source span precedes caller workspace. -/
theorem copyMemory_payload {n b D g p ab bc ac : ℕ} (mem : ℕ → ℕ) (values : List ℤ)
    (hab : ab + n * n ≤ b) (hbc : bc + n * n ≤ b) (hac : ac + n * n ≤ b)
    (vab : ∀ q < n * n, mem (ab + q) = Signed.encode (values.getD q 0))
    (vbc : ∀ q < n * n, mem (bc + q) = Signed.encode (values.getD (n * n + q) 0))
    (vac : ∀ q < n * n, mem (ac + q) = Signed.encode (values.getD (2 * (n * n) + q) 0))
    (q : ℕ) (hq : q < 3 * (n * n)) :
    copyMemory mem b n D g p ab bc ac (b + 5 + q) = Signed.encode (values.getD q 0) := by
  by_cases hfirst : q < n * n
  · unfold copyMemory
    rw [ArrayCopy.copyPrefix_outside (by omega), ArrayCopy.copyPrefix_outside (by omega),
      ArrayCopy.copyPrefix_read hfirst, headerMemory_below _ _ _ _ _ _ _ (by omega)]
    exact vab q hfirst
  · by_cases hsecond : q < 2 * (n * n)
    · have hj : q - n * n < n * n := by omega
      have he : b + 5 + q = b + 5 + n * n + (q - n * n) := by omega
      unfold copyMemory
      rw [ArrayCopy.copyPrefix_outside (by omega), he,
        ArrayCopy.copyPrefix_read hj, ArrayCopy.copyPrefix_outside (by omega),
        headerMemory_below _ _ _ _ _ _ _ (by omega)]
      have hv := vbc (q - n * n) hj
      simpa only [show n * n + (q - n * n) = q by omega] using hv
    · have hj : q - 2 * (n * n) < n * n := by omega
      have he : b + 5 + q = b + 5 + n * n + n * n + (q - 2 * (n * n)) := by omega
      unfold copyMemory
      rw [he, ArrayCopy.copyPrefix_read hj,
        ArrayCopy.copyPrefix_outside (by omega), ArrayCopy.copyPrefix_outside (by omega),
        headerMemory_below _ _ _ _ _ _ _ (by omega)]
      have hv := vac (q - 2 * (n * n)) hj
      simpa only [show 2 * (n * n) + (q - 2 * (n * n)) = q by omega] using hv

/-- The copied words form exactly the existing initialized input block. This is readback of
actual stores and copies, not an input layout supplied to the algorithm. -/
theorem copyMemory_input {n b D g p ab bc ac : ℕ} (mem : ℕ → ℕ) (values : List ℤ)
    (hlen : values.length = 3 * (n * n))
    (hab : ab + n * n ≤ b) (hbc : bc + n * n ≤ b) (hac : ac + n * n ≤ b)
    (vab : ∀ q < n * n, mem (ab + q) = Signed.encode (values.getD q 0))
    (vbc : ∀ q < n * n, mem (bc + q) = Signed.encode (values.getD (n * n + q) 0))
    (vac : ∀ q < n * n, mem (ac + q) = Signed.encode (values.getD (2 * (n * n) + q) 0))
    (q : ℕ) (hq : q < 5 + 3 * (n * n)) :
    copyMemory mem b n D g p ab bc ac (b + q) =
      (Data.init (PreparationInput.input n D g p values) : Data 64).mem q := by
  by_cases hh : q < 5
  · have hhead : copyMemory mem b n D g p ab bc ac (b + q) =
        headerMemory mem b n D g p (b + q) := by
      unfold copyMemory
      rw [ArrayCopy.copyPrefix_outside (by omega), ArrayCopy.copyPrefix_outside (by omega),
        ArrayCopy.copyPrefix_outside (by omega)]
    rw [hhead]
    interval_cases q <;>
      simp [headerMemory, Data.init, PreparationInput.input, hlen, Nat.mul_comm, Nat.add_comm,
        ← Nat.add_assoc]
  · have hr : q - 5 < 3 * (n * n) := by omega
    rw [show b + q = b + 5 + (q - 5) by omega,
      copyMemory_payload mem values hab hbc hac vab vbc vac (q - 5) hr]
    have hv := PreparationInput.input_word n D g p values (q - 5)
    simpa only [show 5 + (q - 5) = q by omega] using hv.symm

end Cslib.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime
