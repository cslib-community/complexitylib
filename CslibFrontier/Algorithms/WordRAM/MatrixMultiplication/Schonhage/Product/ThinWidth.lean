/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Product.Thin
import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Product.ThinEnvelopes

/-!
# Source-regime logarithmic width for actual queried products

## Main results

* `QueriedProduct.thin_envelopes`: original dimensions give polynomial magnitude/address
  envelopes and an explicit polynomial allocation bound.
* `QueriedProduct.thin_admissionWidth_le`: a positive constant times the logarithm of original
  dimension, request count and entry magnitude suffices in the source's thin regime.

These bounds concern the real native program and its actual allocation formulas. They assume
neither intermediate-state fits nor a polynomial-space certificate.
-/

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- The source regime controls every original power, computed band count and address term.
This is the level-`19 * m` case of `thin_envelopes_of_le`. -/
public theorem thin_envelopes (m N Q A : ℕ) (hN : D m ^ 18 ≤ N) :
    magnitudeBound (19 * m) A + wordBudget (19 * m) m N Q + 1 ≤
        2 ^ 40 * (N + Q + A + 2) ^ 10 ∧
      memoryEnd (19 * m) m N Q ≤ 128 * (N + Q + A + 2) ^ 4 :=
  thin_envelopes_of_le (19 * m) m N Q A (by omega) (by omega) hN

/-- A fixed positive logarithmic-width coefficient suffices throughout the thin regime. -/
public theorem thin_admissionWidth_le (m N Q A : ℕ) (hN : D m ^ 18 ≤ N) :
    admissionWidth (19 * m) m N Q A ≤ 128 * Nat.clog 2 (N + Q + A + 2) := by
  let S := N + Q + A + 2
  have hs : 1 < S := by dsimp only [S]; omega
  have hl := Nat.clog_pos (by decide : 1 < (2 : ℕ)) hs
  have hp := Nat.le_pow_clog (by decide : 1 < (2 : ℕ)) S
  have he := (thin_envelopes m N Q A hN).1
  have hpow : magnitudeBound (19 * m) A + wordBudget (19 * m) m N Q + 1 ≤
      2 ^ (40 + 10 * Nat.clog 2 S) := by
    calc _ ≤ 2 ^ 40 * S ^ 10 := he
      _ ≤ 2 ^ 40 * (2 ^ Nat.clog 2 S) ^ 10 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hp 10)
      _ = _ := by rw [pow_add, ← pow_mul, Nat.mul_comm (Nat.clog 2 S) 10]
  have hc := (Nat.clog_le_iff_le_pow (by decide : 1 < (2 : ℕ))).mpr hpow
  unfold admissionWidth
  dsimp only [S] at hc hl
  omega

/-- Complete initialized native thin-product execution at a fixed positive logarithmic-width
threshold. Every original occurrence is answered, including duplicates, and halt is charged.
The occurrence-count condition is stated explicitly rather than replaced by set cardinality. -/
public theorem runs_thin {W m N A : ℕ} (bits : Bool)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (qs : List (Fin N × Fin N)) (hN : D m ^ 18 ≤ N) (hQ : qs.length * 2 ^ m ≤ N ^ 2)
    (hX : ∀ i k, |X i k| ≤ (A : ℤ)) (hY : ∀ k j, |Y k j| ≤ (A : ℤ))
    (hbits : bits = true → (∀ i k, 0 ≤ X i k) ∧ (∀ k j, 0 ≤ Y k j))
    (hW : 128 * Nat.clog 2 (N + qs.length + A + 2) ≤ W) :
    InputFits W (input bits (19 * m) X Y qs) ∧
    ∃ y n,
      Runs W ((program bits).program Reg.output) (State.init (input bits (19 * m) X Y qs))
        ⟨(program bits).size, y⟩ n ∧
      Executes W ((program bits).program Reg.output) (State.init (input bits (19 * m) X Y qs))
        (outputBase (19 * m) m N qs.length) (n + 1) ∧
      ((n + 1 : ℕ) : ℝ) ≤ 4325376 * ((19 * m + 1 : ℕ) : ℝ) * (N : ℝ) ^ 2 /
        (D m : ℝ) ^ (1 / 18 : ℝ) ∧ y.Bounded W ∧
      (∀ i : Fin qs.length, y.mem (outputBase (19 * m) m N qs.length + i.val) =
        Signed.encode ((X * Y) (qs.get i).1 (qs.get i).2)) ∧
      (∀ a, ¬(inputEnd m N qs.length ≤ a ∧ a < memoryEnd (19 * m) m N qs.length) →
        y.mem a = (State.init (input bits (19 * m) X Y qs) : State 160).data.mem a) := by
  obtain ⟨hi, y, n, hn, hr, he, hy, hv, hf⟩ := runs_wide (show m ≤ 19 * m by omega)
    bits X Y qs hX hY hbits ((thin_admissionWidth_le m N qs.length A hN).trans hW)
  have hnR : ((n + 1 : ℕ) : ℝ) ≤ (timeBound (show m ≤ 19 * m by omega) qs + 1 : ℕ) := by
    exact_mod_cast Nat.add_le_add_right hn 1
  exact ⟨hi, y, n, hr, he, hnR.trans (thin_timeBound_sparse m N qs hN hQ), hy, hv, hf⟩

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct
