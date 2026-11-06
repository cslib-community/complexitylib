/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.PrimeSelection.Flat
public import Complexity.Algorithms.WordRAM.ExactTriangle.CountPrime.SourceBounds
import Complexity.Foundations.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Logarithmic source admission and polynomial selection prefixes

In the source regime `D ≤ n`, polynomial original weights give logarithmic physical width
for the complete selector. Every successful wider prefix has a polynomial word and support
bound independent of its chosen physical width. The general execution theorem also supports
`D > n`; only this source-regime simplification uses `D ≤ n`.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.PrimeSelection

open Cslib.WordRAM

private theorem controller_clog_le {n D : ℕ} (hDn : D ≤ n) :
    Nat.clog 2 (4 * (D + 2) * (D + 2) + 5) ≤ 5 * Nat.clog 2 (n + 2) := by
  have hb2 : 4 ≤ (n + 2) ^ 2 := (show 4 ≤ (2 : ℕ) ^ 2 by decide).trans
    (Nat.pow_le_pow_left (by omega : 2 ≤ n + 2) 2)
  have hb3 : 8 ≤ (n + 2) ^ 3 := (show 8 ≤ (2 : ℕ) ^ 3 by decide).trans
    (Nat.pow_le_pow_left (by omega : 2 ≤ n + 2) 3)
  have hs : (D + 2) * (D + 2) ≤ (n + 2) ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul (by omega : D + 2 ≤ n + 2)
      (by omega : D + 2 ≤ n + 2)
  have hB : 4 * (D + 2) * (D + 2) + 5 ≤ (n + 2) ^ 5 := by
    calc
      _ ≤ 8 * (n + 2) ^ 2 := by nlinarith only [hb2, hs]
      _ ≤ (n + 2) ^ 3 * (n + 2) ^ 2 := Nat.mul_le_mul_right _ hb3
      _ = _ := by rw [← pow_add]
  have hp := hB.trans (Nat.pow_le_pow_left
    (Nat.le_pow_clog (by decide : 1 < (2 : ℕ)) (n + 2)) 5)
  rw [← pow_mul, Nat.mul_comm (Nat.clog 2 (n + 2)) 5] at hp
  exact Nat.clog_le_of_le_pow hp

/-- Polynomial original weights and `D ≤ n` give a positive logarithmic threshold for the
actual prime scan and every concrete counter call. No candidate prime is an input. -/
theorem admissionWidth_le_log {n D A κ : ℕ} (hDn : D ≤ n) (hκ : 1 ≤ κ)
    (hA : A ≤ (n + 2) ^ κ) :
    admissionWidth n D A ≤ (κ + 30) * Nat.clog 2 (n + 2) := by
  have hcap : Nat.sqrt D ≤ (n + 2) ^ κ :=
    ((Nat.sqrt_le_self D).trans hDn).trans
      ((by omega : n ≤ n + 2).trans (Nat.le_self_pow (by omega) (n + 2)))
  have hc := CountPrime.admissionWidth_le_log hcap hA
  have hs := controller_clog_le hDn
  unfold admissionWidth
  nlinarith only [hc, hs]

private theorem threshold_pow_le {n D A κ : ℕ} (hDn : D ≤ n) (hκ : 1 ≤ κ)
    (hA : A ≤ (n + 2) ^ κ) :
    2 ^ admissionWidth n D A ≤ (n + 2) ^ (2 * κ + 60) := by
  have hw := admissionWidth_le_log hDn hκ hA
  have htwo : 2 * (n + 2) ≤ (n + 2) ^ 2 := by nlinarith
  calc
    _ ≤ 2 ^ ((κ + 30) * Nat.clog 2 (n + 2)) := Nat.pow_le_pow_right (by decide) hw
    _ = (2 ^ Nat.clog 2 (n + 2)) ^ (κ + 30) := by
      rw [← pow_mul, Nat.mul_comm]
    _ ≤ (2 * (n + 2)) ^ (κ + 30) :=
      Nat.pow_le_pow_left (Nat.pow_clog_le_mul (by decide) (by omega)) _
    _ ≤ ((n + 2) ^ 2) ^ (κ + 30) := Nat.pow_le_pow_left htwo _
    _ = _ := by rw [← pow_mul, Nat.mul_add]

/-- Every actual prefix at every admitted source-regime physical width has polynomial
words and support independently of that physical width. -/
theorem bounded_reachable_polynomial {W n D A κ : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hD : 16 ≤ D) (hDn : D ≤ n) (hκ : 1 ≤ κ)
    (hv : ∀ z ∈ values, z.natAbs ≤ A) (hA : A ≤ (n + 2) ^ κ)
    (hW : (κ + 30) * Nat.clog 2 (n + 2) ≤ W)
    (s : State 160) (steps : ℕ)
    (hr : Runs W (entryProgram.program Reg.best)
      (State.init (CountPrime.inputWords n D values)) s steps) :
    (∀ i, s.data.regs i < (n + 2) ^ (2 * κ + 60)) ∧
      (∀ a, s.data.mem a < (n + 2) ^ (2 * κ + 60)) ∧
      ∀ a, (n + 2) ^ (2 * κ + 60) ≤ a → s.data.mem a = 0 := by
  obtain ⟨regs, memory, support⟩ := bounded_reachable values hlen hD hv
    ((admissionWidth_le_log hDn hκ hA).trans hW) s steps hr
  have hb := threshold_pow_le hDn hκ hA
  exact ⟨fun i => (regs i).trans_le hb, fun a => (memory a).trans_le hb,
    fun a ha => support a (hb.trans ha)⟩

end Cslib.Algorithms.WordRAM.ExactTriangle.PrimeSelection
