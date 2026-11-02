/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.CountPrime.Flat
import Complexity.Foundations.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Original-input logarithmic width and polynomial wider prefixes

When the original modulus and weights are polynomially bounded in n+2, the concrete counter
admits logarithmic physical width and every wider execution has polynomial words and memory
support, independently of that chosen width. The modulus bound is explicit; these are not
uniform bounds for arbitrarily large runtime p relative to n.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime

open Cslib.WordRAM

private theorem padding_le (n : ℕ) : 2 ^ Nat.clog 2 n ≤ (n + 2) ^ 2 := by
  have hm := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ))
    (Nat.clog_mono_right 2 (by omega : n ≤ n + 1))
  have hp := Nat.pow_clog_le_mul (by decide : 1 < (2 : ℕ)) (by omega : n + 1 ≠ 0)
  have hb : 2 * (n + 1) ≤ (n + 2) ^ 2 := by nlinarith
  exact (hm.trans hp).trans hb

private theorem envelope_le_pow {n p A κ : ℕ}
    (hp : p ≤ (n + 2) ^ κ) (hA : A ≤ (n + 2) ^ κ) :
    envelope n p A ≤ (n + 2) ^ (κ + 21) := by
  let b := n + 2
  let k := Nat.clog 2 n
  let e := κ + 12
  change p ≤ b ^ κ at hp
  change A ≤ b ^ κ at hA
  have hb : 2 ≤ b := by dsimp only [b]; omega
  have hb1 : 1 ≤ b := by omega
  have hn : n ≤ b := by dsimp only [b]; omega
  have hk : k ≤ n := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self.le)
  have hκ : 1 ≤ b ^ κ := Nat.one_le_pow _ _ hb1
  have htwo : 2 ^ k ≤ b ^ 2 := padding_le n
  have hfour : 4 ^ k ≤ b ^ 4 := by
    calc
      _ = (2 ^ k) ^ 2 := by rw [pow_two, ← mul_pow]; rfl
      _ ≤ (b ^ 2) ^ 2 := Nat.pow_le_pow_left htwo _
      _ = b ^ 4 := by rw [← pow_mul]
  have hsixteen : 16 ^ k ≤ b ^ 8 := by
    change (2 ^ 4) ^ k ≤ b ^ 8
    rw [← pow_mul, Nat.mul_comm 4 k, pow_mul]
    exact (Nat.pow_le_pow_left htwo 4).trans_eq (by rw [← pow_mul])
  have hN2 : n * n ≤ b ^ e := by
    calc
      _ ≤ b ^ 2 := by simpa only [pow_two] using Nat.mul_le_mul hn hn
      _ ≤ b ^ e := Nat.pow_le_pow_right hb1 (by dsimp only [e]; omega)
  have hN3 : n * n * n ≤ b ^ e := by
    calc
      _ ≤ b ^ 3 := by
        simpa only [pow_succ, pow_zero, one_mul] using (Nat.mul_le_mul (Nat.mul_le_mul hn hn) hn)
      _ ≤ b ^ e := Nat.pow_le_pow_right hb1 (by dsimp only [e]; omega)
  have hnE : n ≤ b ^ e := hn.trans (Nat.le_self_pow (by dsimp only [e]; omega) b)
  have hkE : k ≤ b ^ e := hk.trans hnE
  have hpE : p ≤ b ^ e := hp.trans (Nat.pow_le_pow_right hb1 (by dsimp only [e]; omega))
  have hAE : A ≤ b ^ e := hA.trans (Nat.pow_le_pow_right hb1 (by dsimp only [e]; omega))
  have hfourE : 4 ^ k ≤ b ^ e := hfour.trans
    (Nat.pow_le_pow_right hb1 (by dsimp only [e]; omega))
  have htwoE : 2 ^ k ≤ b ^ e := htwo.trans
    (Nat.pow_le_pow_right hb1 (by dsimp only [e]; omega))
  have harea : 4 ^ k * p ≤ b ^ e := by
    calc
      _ ≤ b ^ 4 * b ^ κ := Nat.mul_le_mul hfour hp
      _ = b ^ (κ + 4) := by rw [← pow_add, Nat.add_comm]
      _ ≤ b ^ e := Nat.pow_le_pow_right hb1 (by dsimp only [e]; omega)
  have hunit : 1 ≤ b ^ e := Nat.one_le_pow _ _ hb1
  have hconst : 16 ≤ b ^ e := (show 16 ≤ (2 : ℕ) ^ 12 by decide).trans
    ((Nat.pow_le_pow_left hb 12).trans (Nat.pow_le_pow_right hb1 (by dsimp only [e]; omega)))
  have hB : addressBudget n p k (3 + 3 * (n * n)) 3 (3 + n * n)
      (3 + 2 * (n * n)) ≤ 480 * b ^ e := by
    unfold addressBudget
    nlinarith only [hN2, hN3, hnE, hkE, hpE, hfourE, htwoE, harea, hconst]
  have hcoeff : 10 ≤ b ^ 4 := (show 10 ≤ (2 : ℕ) ^ 4 by decide).trans
    (Nat.pow_le_pow_left hb 4)
  have hmag : 2 * (p + 4) * 16 ^ k ≤ b ^ e := by
    calc
      _ ≤ (10 * b ^ κ) * b ^ 8 := Nat.mul_le_mul (by omega) hsixteen
      _ = 10 * b ^ (κ + 8) := by rw [pow_add]; ring
      _ ≤ b ^ 4 * b ^ (κ + 8) := Nat.mul_le_mul_right _ hcoeff
      _ = b ^ e := by rw [← pow_add]; congr 1; dsimp only [e]; omega
  have hE : envelope n p A ≤ 485 * b ^ e := by
    unfold envelope magnitudeBudget
    change addressBudget n p k (3 + 3 * (n * n)) 3 (3 + n * n)
      (3 + 2 * (n * n)) + (A + p + 2 * (p + 4) * 16 ^ k + 1) + 1 ≤ _
    omega
  have h485 : 485 ≤ b ^ 9 := (show 485 ≤ (2 : ℕ) ^ 9 by decide).trans
    (Nat.pow_le_pow_left hb 9)
  calc
    envelope n p A ≤ 485 * b ^ e := hE
    _ ≤ b ^ 9 * b ^ e := Nat.mul_le_mul_right _ h485
    _ = b ^ (κ + 21) := by rw [← pow_add]; congr 1; dsimp only [e]; omega

/-- Polynomial original moduli and weights give a positive logarithmic physical threshold,
including input fit and both signed-kernel extension bits. Empty matrices are included. -/
theorem admissionWidth_le_log {n p A κ : ℕ}
    (hp : p ≤ (n + 2) ^ κ) (hA : A ≤ (n + 2) ^ κ) :
    admissionWidth n p A ≤ (κ + 24) * Nat.clog 2 (n + 2) := by
  have hpow := (envelope_le_pow hp hA).trans
    (Nat.pow_le_pow_left (Nat.le_pow_clog (by decide : 1 < (2 : ℕ)) (n + 2)) (κ + 21))
  rw [← pow_mul] at hpow
  have hc := Nat.clog_le_of_le_pow hpow
  have hpos : 1 ≤ Nat.clog 2 (n + 2) := Nat.clog_pos (by decide) (by omega)
  unfold admissionWidth
  nlinarith only [hc, hpos]

/-- The same original hypotheses bound words and memory support by one polynomial independent
of the admitted physical width. -/
theorem wordBound_le_pow {n p A κ : ℕ}
    (hp : p ≤ (n + 2) ^ κ) (hA : A ≤ (n + 2) ^ κ) :
    wordBound n p A ≤ (n + 2) ^ (κ + 25) := by
  have hc : 16 ≤ (n + 2) ^ 4 := (show 16 ≤ (2 : ℕ) ^ 4 by decide).trans
    (Nat.pow_le_pow_left (by omega : 2 ≤ n + 2) 4)
  calc
    _ ≤ (n + 2) ^ 4 * (n + 2) ^ (κ + 21) := Nat.mul_le_mul hc (envelope_le_pow hp hA)
    _ = _ := by rw [← pow_add]; congr 1; omega

/-- Every actual prefix at any sufficiently wide source-regime width has polynomial words
and support, not merely a bound by that physical width's own word universe. -/
theorem bounded_reachable_polynomial {W n p A κ : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hp0 : 0 < p)
    (hv : ∀ z ∈ values, z.natAbs ≤ A)
    (hp : p ≤ (n + 2) ^ κ) (hA : A ≤ (n + 2) ^ κ)
    (hW : (κ + 24) * Nat.clog 2 (n + 2) ≤ W)
    (s : State 128) (steps : ℕ)
    (hr : Runs W (entryProgram.program Reg.result) (State.init (inputWords n p values)) s steps) :
    (∀ i, s.data.regs i < (n + 2) ^ (κ + 25)) ∧
      (∀ a, s.data.mem a < (n + 2) ^ (κ + 25)) ∧
      ∀ a, (n + 2) ^ (κ + 25) ≤ a → s.data.mem a = 0 := by
  obtain ⟨regs, memory, support⟩ := bounded_reachable values hlen hp0 hv
    ((admissionWidth_le_log hp hA).trans hW) s steps hr
  have hb := wordBound_le_pow hp hA
  exact ⟨fun i => (regs i).trans_le hb, fun a => (memory a).trans_le hb,
    fun a ha => support a (hb.trans ha)⟩

end Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime
