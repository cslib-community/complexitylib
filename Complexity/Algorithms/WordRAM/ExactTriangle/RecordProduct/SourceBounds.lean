/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.RecordProduct.Flat
public import Complexity.Algorithms.WordRAM.ExactTriangle.PreparationBounds

/-!
# Original-size prefix bounds and the per-record thin saving

The initialized code has physical-width-independent polynomial words and memory support at
every admitted wider width. Its charge is the actual producer preparation plus the selected
record's actual thin product. Summing all products, solving ExactTriangle and reconstructing
witnesses remain separate; no aggregate subcubic claim is made here.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordProduct

open Cslib.WordRAM Cslib.Algorithms.ExactTriangle
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Explicit input-derived bound for all prefix words and the address support, independent
of any larger admitted physical width. This is a reservation, not a bulk initialization. -/
@[expose] def wordBound (n D g p A : ℕ) : ℕ := 2 ^ admissionWidth n D g p A

/-- The prefix bound is polynomial in original size for the usual original scalar/weight
envelopes, with an explicit fixed exponent for each magnitude exponent κ. -/
theorem wordBound_le_pow {n D g p A κ : ℕ} (hn : 1 ≤ n)
    (hD : D ≤ n) (hg : g ≤ n) (hp : p ≤ n) (hA : A ≤ (n + 2) ^ κ) :
    wordBound n D g p A ≤ (n + 2) ^ (514 * κ + 11812) := by
  let b := n + 2
  have hb : 1 < b := by dsimp only [b]; omega
  have hc := Nat.clog_pos (by decide : 1 < (2 : ℕ)) hb
  have hp2 := Nat.pow_pred_clog_lt_self (by decide : 1 < (2 : ℕ)) hb
  have he : Nat.clog 2 b = (Nat.clog 2 b).pred + 1 := (Nat.succ_pred_eq_of_pos hc).symm
  have hbase : 2 ^ Nat.clog 2 b ≤ b ^ 2 := by
    rw [he, pow_succ]
    nlinarith only [hp2, show 2 ≤ b by omega]
  have hw := admissionWidth_le_log hn hD hg hp hA
  have hpow := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hw
  change 2 ^ admissionWidth n D g p A ≤ _
  calc
    _ ≤ 2 ^ ((257 * κ + 5906) * Nat.clog 2 b) := hpow
    _ = (2 ^ Nat.clog 2 b) ^ (257 * κ + 5906) := by rw [← Nat.pow_mul, Nat.mul_comm]
    _ ≤ (b ^ 2) ^ (257 * κ + 5906) := Nat.pow_le_pow_left hbase _
    _ = b ^ (514 * κ + 11812) := by
      rw [← Nat.pow_mul]
      exact congrArg (fun k : ℕ => b ^ k) (by omega : 2 * (257 * κ + 5906) = 514 * κ + 11812)

/-- Every actual native prefix at every admitted width has input-derived bounded words and
zero memory beyond the same bound. The real halting run at the minimum admitted width and
the existing width-independent prefix theorem derive the result. -/
theorem bounded_reachable_original {W m n g p A k : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hD : 16 ≤ D m)
    (hg : 1 ≤ g) (hp : 0 < p) (hN : D m ^ 18 ≤ n)
    (hv : ∀ z ∈ values, z.natAbs ≤ A) (hW : admissionWidth n (D m) g p A ≤ W)
    {s : State 320} (hr : Runs W (entryProgram.program Reg.result)
      (State.init (PreparationInput.input n (D m) g p values)) s k) :
    (∀ i, s.data.regs i < wordBound n (D m) g p A) ∧
      (∀ a, s.data.mem a < wordBound n (D m) g p A) ∧
      ∀ a, wordBound n (D m) g p A ≤ a → s.data.mem a = 0 := by
  obtain ⟨hi, a, idx, ha, hidx, hord, y, t, ht, hpref, he, hy, yr, hv', hf, hreg, hQ⟩ :=
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

/-- Complete producer preparation plus one actual record product, including the final halt.
The per-record sparsity is supplied by its actual native chunk, not an aggregate solver oracle. -/
theorem initialized_time_le {m n g p : ℕ} (values : List ℤ) (qs : List (Fin n × Fin n))
    (hD : 16 ≤ D m) (hN : D m ^ 18 ≤ n) (hg : 1 ≤ g)
    (hp : p ∈ Nat.sqrtPrimeWindow (D m)) (hQ : qs.length * 2 ^ m ≤ n ^ 2) :
    ((preparationTime n (D m) g p values + timeBound (m := m) qs + 1 : ℕ) : ℝ) ≤
      690 * (n : ℝ) ^ 2 * D m * g +
        34603008 * ((19 * m + 1 : ℕ) : ℝ) * (n : ℝ) ^ 2 / (D m : ℝ) ^ (1 / 18 : ℝ) := by
  have hDn : D m ≤ n := (Nat.le_self_pow (by decide : 18 ≠ 0) (D m)).trans hN
  have hpTime := PreparationBounds.computed_timeBound_le values hD hDn hg hp
  have hpReal : (preparationTime n (D m) g p values : ℝ) ≤
      690 * (n : ℝ) ^ 2 * D m * g := by
    have hpNat : preparationTime n (D m) g p values ≤ 690 * n ^ 2 * D m * g := by
      simpa only [preparationTime, pow_two] using hpTime
    exact_mod_cast hpNat
  have ht := thin_timeBound_sparse qs hN hQ
  push_cast
  push_cast at ht
  linarith only [hpReal, ht]

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordProduct
