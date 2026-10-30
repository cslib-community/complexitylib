/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.FixedPrime.Flat
import Complexity.Foundations.Data.Nat.Log

/-!
# Original-input bounds for every fixed-prime native prefix

The admission remains logarithmic for polynomial original weights and bounded scalar headers.
The actual minimum-width halting run controls all wider prefixes, including dirty loads and
all reused-workspace calls. The support envelope is independent of the physical width, and
does not instruct the machine to clear or snapshot that range.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.FixedPrime

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- A fixed original-input bound for all prefix words and memory support. -/
@[expose] def wordBound (n D g p A : ℕ) : ℕ := 2 ^ admissionWidth n D g p A

/-- The all-record controller retains an explicit polynomial envelope for each weight exponent. -/
theorem wordBound_le_pow {n D g p A κ : ℕ} (hn : 1 ≤ n)
    (hD : D ≤ n) (hg : g ≤ n) (hp : p ≤ n) (hA : A ≤ (n + 2) ^ κ) :
    wordBound n D g p A ≤ (n + 2) ^ (514 * κ + 11818) := by
  let b := n + 2
  have hb : 2 ≤ b := by dsimp only [b]; omega
  have hbase : 2 ^ Nat.clog 2 b ≤ b ^ 2 :=
    (Nat.pow_clog_le_mul (by decide : 1 < (2 : ℕ)) (by omega : b ≠ 0)).trans
      (by nlinarith only [hb])
  have hw := admissionWidth_le_log hn hD hg hp hA
  change 2 ^ admissionWidth n D g p A ≤ _
  calc
    _ ≤ 2 ^ ((257 * κ + 5909) * Nat.clog 2 b) := Nat.pow_le_pow_right (by decide) hw
    _ = (2 ^ Nat.clog 2 b) ^ (257 * κ + 5909) := by rw [← Nat.pow_mul, Nat.mul_comm]
    _ ≤ (b ^ 2) ^ (257 * κ + 5909) := Nat.pow_le_pow_left hbase _
    _ = b ^ (514 * κ + 11818) := by
      rw [← Nat.pow_mul]
      exact congrArg (fun j : ℕ => b ^ j) (by omega : 2 * (257 * κ + 5909) = 514 * κ + 11818)

/-- Every actually reached state at every admitted wider width has the same original-input
polynomial word/support envelope. The concrete minimum-width run, not an assumed execution
certificate, supplies the comparison run. -/
theorem bounded_reachable_original {W m n g p A k : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hD : 16 ≤ D m)
    (hg : 1 ≤ g) (hp : p ∈ Nat.sqrtPrimeWindow (D m)) (hN : D m ^ 18 ≤ n)
    (hv : ∀ z ∈ values, z.natAbs ≤ A) (hW : admissionWidth n (D m) g p A ≤ W)
    {s : State 416} (hr : Runs W (program.program Reg.found)
      (State.init (PreparationInput.input n (D m) g p values)) s k) :
    (∀ i, s.data.regs i < wordBound n (D m) g p A) ∧
      (∀ a, s.data.mem a < wordBound n (D m) g p A) ∧
      ∀ a, wordBound n (D m) g p A ≤ a → s.data.mem a = 0 := by
  obtain ⟨hi, a, ha, hout, y, t, ht, hpref, he, -⟩ :=
    runs_input values hlen hD hg hp hN hv le_rfl
  have hlow := Runs.prefix_at_smaller_width program_fixed.2 hW hr he
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

end Cslib.Algorithms.WordRAM.ExactTriangle.FixedPrime
