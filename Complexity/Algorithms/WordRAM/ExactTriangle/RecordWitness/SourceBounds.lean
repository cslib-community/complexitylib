/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.RecordWitness.Flat

/-!
# Original-size width and prefix bounds for candidate recovery

The complete initialized producer/product/verifier has one positive logarithmic physical-width
threshold for polynomial original scalars and weights. Its words and memory support at every
prefix have a polynomial bound independent of any larger physical width. These are consequences
of the actual minimum-width halting run and existing native width transport.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordWitness

open Cslib.WordRAM Cslib.Algorithms.ExactTriangle
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage

/-- Every admitted physical width can be chosen logarithmic in original size. The positive
constant is explicit for each original magnitude exponent; geometry is not weakened. -/
theorem admissionWidth_le_log {n D g p A κ : ℕ} (hn : 1 ≤ n)
    (hD : D ≤ n) (hg : g ≤ n) (hp : p ≤ n) (hA : A ≤ (n + 2) ^ κ) :
    admissionWidth n D g p A ≤ (257 * κ + 5909) * Nat.clog 2 (n + 2) := by
  let b := n + 2
  let E := 2 * κ + 512
  have hb : 2 ≤ b := by dsimp only [b]; omega
  have hb1 : 1 ≤ b := le_trans (by decide : 1 ≤ (2 : ℕ)) hb
  have hP : PreparationInput.wordBound n D g p A ≤ b ^ E := by
    exact (PreparationInput.wordBound_le_pow hn hD hg hp hA).trans
      (Nat.pow_le_pow_right hb1 (by dsimp only [E]; omega))
  have hfour : 2 * (n + n ^ 2 + 3) ≤ b ^ 4 := by
    dsimp only [b]
    nlinarith only [Nat.zero_le (n ^ 4), Nat.zero_le (n ^ 3), Nat.zero_le (n ^ 2),
      Nat.zero_le n]
  have hfour' : 2 * (n + n ^ 2 + 3) ≤ (b ^ 2) ^ 2 := hfour.trans_eq (Nat.pow_mul b 2 2)
  have hM : CallableProduct.windowSize n (n ^ 2) ≤ b ^ E := by
    calc
      _ ≤ (2 * (n + n ^ 2 + 3)) ^ 128 := CallableProduct.windowSize_le n (n ^ 2)
      _ ≤ ((b ^ 2) ^ 2) ^ 128 := Nat.pow_le_pow_left hfour' _
      _ = (b ^ 2) ^ 256 := (Nat.pow_mul (b ^ 2) 2 128).symm
      _ ≤ (b ^ 2) ^ (κ + 256) := Nat.pow_le_pow_right (Nat.pow_pos hb1)
        (Nat.le_add_left 256 κ)
      _ = b ^ E := by
        rw [← Nat.pow_mul]
        exact congrArg (fun j : ℕ => b ^ j)
          (by dsimp only [E]; omega : 2 * (κ + 256) = E)
  have hn2 : n ^ 2 ≤ b ^ E := (Nat.pow_le_pow_left (by dsimp only [b]; omega : n ≤ b) 2).trans
    (Nat.pow_le_pow_right hb1 (by dsimp only [E]; omega))
  have hnE : n ≤ b ^ E := (show n ≤ n ^ 2 by nlinarith only [hn]).trans hn2
  have hprod : n * D ≤ b ^ E := (Nat.mul_le_mul_left n hD).trans
    (by simpa only [pow_two] using hn2)
  have hAE : A ≤ b ^ E := hA.trans
    (Nat.pow_le_pow_right hb1 (by dsimp only [E]; omega))
  have hconst : 4096 ≤ b ^ E := (show 4096 ≤ (2 : ℕ) ^ 12 by decide).trans
    ((Nat.pow_le_pow_left hb 12).trans
      (Nat.pow_le_pow_right hb1 (by dsimp only [E]; omega)))
  have hsum : envelope n D g p A ≤ 576 * b ^ E := by
    unfold envelope
    have hgE := hg.trans hnE
    have hDE := hD.trans hnE
    omega
  have henvelope : envelope n D g p A ≤ b ^ (2 * κ + 522) := by
    calc
      _ ≤ 576 * b ^ E := hsum
      _ ≤ b ^ 10 * b ^ E := Nat.mul_le_mul_right _
        ((show 576 ≤ (2 : ℕ) ^ 10 by decide).trans (Nat.pow_le_pow_left hb 10))
      _ = b ^ (2 * κ + 522) := by
        rw [← Nat.pow_add]
        exact congrArg (fun j : ℕ => b ^ j) (by dsimp only [E]; omega : 10 + E = 2 * κ + 522)
  have hbase := Nat.le_pow_clog (by decide : 1 < (2 : ℕ)) b
  have hlogBound := henvelope.trans (Nat.pow_le_pow_left hbase (2 * κ + 522))
  rw [← Nat.pow_mul] at hlogBound
  have hlog := Nat.clog_le_of_le_pow hlogBound
  change Nat.clog 2 (envelope n D g p A) ≤ Nat.clog 2 b * (2 * κ + 522) at hlog
  have hrecord := RecordProduct.admissionWidth_le_log hn hD hg hp hA
  have hlog' : Nat.clog 2 (envelope n D g p A) ≤ (257 * κ + 5906) * Nat.clog 2 b := by
    nlinarith only [hlog, Nat.zero_le (κ * Nat.clog 2 b)]
  have hmax := max_le hrecord hlog'
  have hpositive : 1 ≤ Nat.clog 2 b := Nat.clog_pos (by decide) (by omega : 1 < b)
  unfold admissionWidth
  dsimp only [b] at hmax hpositive
  nlinarith only [hmax, hpositive]

/-- Original-input prefix word/address envelope, independent of the caller's larger width. -/
@[expose] def wordBound (n D g p A : ℕ) : ℕ := 2 ^ admissionWidth n D g p A

/-- All prefix words and memory support have a fixed polynomial envelope for each κ. -/
theorem wordBound_le_pow {n D g p A κ : ℕ} (hn : 1 ≤ n)
    (hD : D ≤ n) (hg : g ≤ n) (hp : p ≤ n) (hA : A ≤ (n + 2) ^ κ) :
    wordBound n D g p A ≤ (n + 2) ^ (514 * κ + 11818) := by
  let b := n + 2
  have hb : 1 < b := by dsimp only [b]; omega
  have hc := Nat.clog_pos (by decide : 1 < (2 : ℕ)) hb
  have hp2 := Nat.pow_pred_clog_lt_self (by decide : 1 < (2 : ℕ)) hb
  have he : Nat.clog 2 b = (Nat.clog 2 b).pred + 1 := (Nat.succ_pred_eq_of_pos hc).symm
  have hbase : 2 ^ Nat.clog 2 b ≤ b ^ 2 := by
    rw [he, pow_succ]
    nlinarith only [hp2, show 2 ≤ b by omega]
  have hw := admissionWidth_le_log hn hD hg hp hA
  change 2 ^ admissionWidth n D g p A ≤ _
  calc
    _ ≤ 2 ^ ((257 * κ + 5909) * Nat.clog 2 b) := Nat.pow_le_pow_right (by decide) hw
    _ = (2 ^ Nat.clog 2 b) ^ (257 * κ + 5909) := by rw [← Nat.pow_mul, Nat.mul_comm]
    _ ≤ (b ^ 2) ^ (257 * κ + 5909) := Nat.pow_le_pow_left hbase _
    _ = b ^ (514 * κ + 11818) := by
      rw [← Nat.pow_mul]
      exact congrArg (fun j : ℕ => b ^ j) (by omega : 2 * (257 * κ + 5909) = 514 * κ + 11818)

/-- At every admitted wider width, every actual prefix has original-input polynomial words
and zero memory above the same original-input envelope. Dirty pre-normalization loads are
included because the entire actual native execution is compared with its minimum-width run. -/
theorem bounded_reachable_original {W m n g p A k : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hD : 16 ≤ D m)
    (hg : 1 ≤ g) (hp : p ∈ Nat.sqrtPrimeWindow (D m)) (hN : D m ^ 18 ≤ n)
    (hv : ∀ z ∈ values, z.natAbs ≤ A) (hW : admissionWidth n (D m) g p A ≤ W)
    {s : State 400} (hr : Runs W (entryProgram.program Reg.found)
      (State.init (PreparationInput.input n (D m) g p values)) s k) :
    (∀ i, s.data.regs i < wordBound n (D m) g p A) ∧
      (∀ a, s.data.mem a < wordBound n (D m) g p A) ∧
      ∀ a, wordBound n (D m) g p A ≤ a → s.data.mem a = 0 := by
  obtain ⟨hi, a, idx, ha, hout, hidx, hord, y, t, S, ht, hpref, he, -⟩ :=
    runs_input values hlen hD hg hp hN hv le_rfl
  have hlow := Runs.prefix_at_smaller_width entryProgram_fixed.2 hW hr he
  have hs := hlow.bounded (Data.Bounded.init hi)
  refine ⟨hs.1, hs.2, ?_⟩
  intro a ha
  rw [hlow.mem_above (Data.Bounded.init hi) ha]
  cases a with
  | zero =>
    change 2 ^ admissionWidth n (D m) g p A ≤ 0 at ha
    have := Nat.two_pow_pos (admissionWidth n (D m) g p A)
    omega
  | succ a =>
    change (PreparationInput.input n (D m) g p values).getD a 0 = 0
    apply List.getD_eq_default
    have hlen := hi.1
    dsimp only [Fits] at hlen
    change 2 ^ admissionWidth n (D m) g p A ≤ a + 1 at ha
    omega

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordWitness
