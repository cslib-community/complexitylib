/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.Decision.Program
public import Complexity.Algorithms.WordRAM.ThreeSum.Host.Width

/-!
# Logarithmic physical width for the complete ordinary host

The coefficient depends only on the fixed magnitude exponent and the concrete finite callee.
It covers the native computation of the preprocessing word envelope, the disjoint matrix arena,
and the callee's actual logarithmic-width obligation. No width depends on input values.

## Main definitions

* `widthCoefficient`, `width`: positive uniform physical-width threshold.

## Main results

* `preprocessing_width_le`: reuse the complete preprocessing threshold.
* `margin_fits`: polynomial envelope with three extra signed representation bits.
* `callee_width`: the actual free pointer, filler and side satisfy the concrete callee contract.

These coarse polynomial bounds are original.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Decision

open Cslib.WordRAM

/-- A constant for fixed exponent and concrete callee, independent of length and word width. -/
def widthCoefficient (κ d : ℕ) : ℕ :=
  1300 * κ + 7865 + (d + 1) * (envelopeExponent κ + 20) + 20

/-- Positive logarithmic physical width, including empty inputs. -/
def width (κ d n : ℕ) : ℕ := widthCoefficient κ d * Nat.clog 2 (n + 2)

/-- This native width is positive for every length and exponent. -/
theorem width_pos (κ d n : ℕ) : 0 < width κ d n := by
  have hL : 0 < Nat.clog 2 (n + 2) := Nat.clog_pos (by decide) (by omega)
  dsimp only [width, widthCoefficient]
  positivity

/-- The complete preprocessing's physical threshold is covered. -/
theorem preprocessing_width_le (κ d n : ℕ) : ChanHe.Preprocessing.width κ n ≤ width κ d n := by
  rw [ChanHe.Preprocessing.width_eq]
  exact Nat.mul_le_mul_right _ (by dsimp only [widthCoefficient]; omega)

/-- Enough physical bits remain for the signed compiler's two bits and its signed range. -/
theorem four_le_width (κ d n : ℕ) : 4 ≤ width κ d n := by
  have hL : 1 ≤ Nat.clog 2 (n + 2) := Nat.clog_pos (by decide) (by omega)
  have hC : 4 ≤ widthCoefficient κ d := by dsimp only [widthCoefficient]; omega
  exact hC.trans (by
    simpa only [width, Nat.mul_one] using Nat.mul_le_mul_left (widthCoefficient κ d) hL)

/-- A polynomial envelope for every local caller arithmetic result fits with a signed margin. -/
theorem margin_fits {κ d n w : ℕ} (hw : width κ d n ≤ w) :
    Fits (w - 3) ((n + 2) ^ (envelopeExponent κ + 5)) := by
  let L := Nat.clog 2 (n + 2)
  have hL : 1 ≤ L := Nat.clog_pos (by decide) (by omega)
  have hb : n + 2 ≤ 2 ^ L := Nat.le_pow_clog (by decide) _
  have hq : (n + 2) ^ (envelopeExponent κ + 5) ≤
      2 ^ ((envelopeExponent κ + 5) * L) := by
    simpa only [← pow_mul, Nat.mul_comm] using Nat.pow_le_pow_left hb (envelopeExponent κ + 5)
  have hwide : (envelopeExponent κ + 5) * L + 4 ≤ w := by
    have hC : envelopeExponent κ + 9 ≤ widthCoefficient κ d := by
      dsimp only [widthCoefficient]
      nlinarith
    have hh := Nat.mul_le_mul_right L hC
    change widthCoefficient κ d * L ≤ w at hw
    nlinarith
  exact hq.trans_lt (Nat.pow_lt_pow_right (by decide) (by omega))

/-- Thirty-two times the reservation remains within the small extra polynomial margin. -/
theorem reservation_margin (κ n : ℕ) :
    32 * (n + 2) ^ envelopeExponent κ ≤ (n + 2) ^ (envelopeExponent κ + 5) := by
  rw [pow_add]
  have h5 : 32 ≤ (n + 2) ^ 5 := by
    exact (by norm_num : 32 = 2 ^ 5) ▸ Nat.pow_le_pow_left (by omega : 2 ≤ n + 2) 5
  simpa only [Nat.mul_comm] using Nat.mul_le_mul_left ((n + 2) ^ envelopeExponent κ) h5

/-- The actual matrix arena, filler and side meet the finite callee's width guarantee. -/
theorem callee_width {κ d n N w : ℕ} (hN : N < (n + 2) ^ envelopeExponent κ)
    (hw : width κ d n ≤ w) :
    d * Nat.clog 2 (2 * (n + 2) ^ envelopeExponent κ +
      3 * (Host.sideLength N * Host.sideLength N) +
      (2 * (n + 2) ^ envelopeExponent κ + 1) + Host.sideLength N + 2) ≤ w := by
  let V := (n + 2) ^ envelopeExponent κ
  let L := Nat.clog 2 (n + 2)
  have hV : 1 ≤ V := Nat.one_le_pow _ _ (by omega)
  have ha := Host.area_le N
  have ht : Host.sideLength N ≤ N + 1 := by
    dsimp only [Host.sideLength]
    exact Nat.add_le_add_right (Nat.sqrt_le_self N) 1
  have hsize : 2 * V + 3 * (Host.sideLength N * Host.sideLength N) +
      (2 * V + 1) + Host.sideLength N + 2 ≤ 32 * V := by omega
  have hbound := hsize.trans (reservation_margin κ n)
  have hpow : (n + 2) ^ (envelopeExponent κ + 5) ≤
      2 ^ ((envelopeExponent κ + 5) * L) := by
    simpa only [← pow_mul, Nat.mul_comm] using
      Nat.pow_le_pow_left (Nat.le_pow_clog (by decide : 1 < 2) (n + 2)) (envelopeExponent κ + 5)
  have hc := Nat.clog_le_of_le_pow (hbound.trans hpow)
  have hL : 1 ≤ L := Nat.clog_pos (by decide) (by omega)
  have hd : d * (envelopeExponent κ + 5) * L ≤ w := by
    have hC : d * (envelopeExponent κ + 5) ≤ widthCoefficient κ d := by
      dsimp only [widthCoefficient]
      nlinarith
    exact (Nat.mul_le_mul_right L hC).trans hw
  exact (Nat.mul_le_mul_left d hc).trans (by simpa only [Nat.mul_assoc] using hd)

/-- Every integer in the polynomial margin fits the signed source width. -/
theorem signed_margin {κ d n w : ℕ} (hw : width κ d n ≤ w) (z : ℤ)
    (hz : |z| ≤ ((n + 2) ^ (envelopeExponent κ + 5) : ℕ)) :
    Cslib.GenericRAM.Signed.Fits (w - 2) z := by
  have hf := margin_fits hw
  have hw4 := (four_le_width κ d n).trans hw
  have hp : (((n + 2) ^ (envelopeExponent κ + 5) : ℕ) : ℤ) <
      (2 : ℤ) ^ (w - 3) := by exact_mod_cast hf
  have he : w - 2 - 1 = w - 3 := by omega
  obtain ⟨hlo, hhi⟩ := abs_le.mp hz
  exact ⟨by omega, by rw [he]; omega, by rw [he]; omega⟩

/-- The runtime exponent and every power-loop result fit without an extra input premise. -/
theorem reservation_fits {κ d n w : ℕ} (hw : width κ d n ≤ w) :
    Fits w ((n + 2) ^ envelopeExponent κ) ∧ Fits w (envelopeExponent κ) ∧
      Fits w (n + 2) ∧ Fits w 3 := by
  let V := (n + 2) ^ envelopeExponent κ
  have hV : 1 ≤ V := Nat.one_le_pow _ _ (by omega)
  have hE : envelopeExponent κ ≤ V := by
    exact (Nat.lt_two_pow_self (n := envelopeExponent κ)).le.trans
      (Nat.pow_le_pow_left (by omega : 2 ≤ n + 2) _)
  have hB : n + 2 ≤ V := by
    exact (by simp : n + 2 = (n + 2) ^ 1) ▸
      Nat.pow_le_pow_right (by omega) (by dsimp only [envelopeExponent]; omega)
  have hf := (margin_fits hw).mono (show w - 3 ≤ w by omega)
  have hm := reservation_margin κ n
  exact ⟨hf.of_le (by omega), hf.of_le (by omega),
    hf.of_le (by omega), hf.of_le (by omega)⟩

/-- All local caller premises follow from the single global logarithmic threshold. -/
theorem caller_fits {κ d n N w : ℕ} (hN : N < (n + 2) ^ envelopeExponent κ)
    (hw : width κ d n ≤ w) :
    let V := (n + 2) ^ envelopeExponent κ
    (∀ s < 2 * Host.sideLength N, Cslib.GenericRAM.Signed.Fits (w - 2)
      ((2 * (Host.sideLength N * Host.sideLength N) + s + 1 : ℕ) : ℤ)) ∧
    Cslib.GenericRAM.Signed.Fits (w - 2) (2 * (V : ℤ) + 1) ∧
    Cslib.GenericRAM.Signed.Fits (w - 2) (-(2 * (V : ℤ) + 1)) ∧
    (∀ z : ℤ, |z| ≤ (V : ℤ) → Cslib.GenericRAM.Signed.Fits (w - 2) z) ∧
    Fits w (2 * V + 3 * (Host.sideLength N * Host.sideLength N)) ∧
    Fits w (4 * V + 2) ∧ Fits w (4 * N + 4) ∧ Fits w (2 * V) := by
  let V := (n + 2) ^ envelopeExponent κ
  have hV : 1 ≤ V := Nat.one_le_pow _ _ (by omega)
  have ha := Host.area_le N
  have ht : Host.sideLength N ≤ N + 1 := by
    dsimp only [Host.sideLength]
    exact Nat.add_le_add_right (Nat.sqrt_le_self N) 1
  have hm := reservation_margin κ n
  have hf := (margin_fits hw).mono (show w - 3 ≤ w by omega)
  refine ⟨?_, ?_, ?_, ?_, hf.of_le (by omega), hf.of_le (by omega),
    hf.of_le (by omega), hf.of_le (by omega)⟩
  · intro s hs
    apply signed_margin hw
    rw [abs_of_nonneg (by positivity)]
    exact_mod_cast (show 2 * (Host.sideLength N * Host.sideLength N) + s + 1 ≤
      (n + 2) ^ (envelopeExponent κ + 5) by omega)
  · apply signed_margin hw
    rw [abs_of_nonneg (by positivity)]
    exact_mod_cast (show 2 * V + 1 ≤ (n + 2) ^ (envelopeExponent κ + 5) by omega)
  · apply signed_margin hw
    rw [abs_neg, abs_of_nonneg (by positivity)]
    exact_mod_cast (show 2 * V + 1 ≤ (n + 2) ^ (envelopeExponent κ + 5) by omega)
  · intro z hz
    apply signed_margin hw
    exact hz.trans (by exact_mod_cast (show V ≤ (n + 2) ^ (envelopeExponent κ + 5) by omega))

end Cslib.Algorithms.WordRAM.ThreeSum.Decision
