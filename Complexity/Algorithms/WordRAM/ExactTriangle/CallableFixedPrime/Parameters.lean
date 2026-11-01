/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.FixedPrime

/-!
# Computable source width for the callable fixed-prime solver

The adapter accumulates the actual unsigned input words while copying the three original
matrices. Its source width depends on that sum and the original scalar arguments, without
a supplied exponent, logarithm, intermediate layout or execution certificate. The large
constant is a conservative width bound, not an additional charged polynomial computation.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime

open Cslib.WordRAM
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage

/-- Width computed from the original scalars and the actual copied raw-word sum. -/
@[expose] def sourceWidth (n D g p total : ℕ) : ℕ :=
  6166 * Nat.clog 2 (n + D + g + p + total + 4)

/-- A virtual address reservation; the program never clears or snapshots this interval. -/
@[expose] def windowSize (n D g p total : ℕ) : ℕ := 2 ^ sourceWidth n D g p total

private theorem admission_mono {n D g p A B : ℕ}
    (hn : n ≤ B) (hD : D ≤ B) (hg : g ≤ B) (hp : p ≤ B) (hA : A ≤ B) :
    FixedPrime.admissionWidth n D g p A ≤ FixedPrime.admissionWidth B B B B B := by
  have henv : PreparationInput.envelope n D g p A ≤ PreparationInput.envelope B B B B B := by
    dsimp only [PreparationInput.envelope, Instances.budget, Catalogue.budget]
    gcongr
  have hw : PreparationInput.width n D g p A ≤ PreparationInput.width B B B B B :=
    Nat.add_le_add_right (Nat.clog_mono_right 2 henv) 3
  have hP : PreparationInput.wordBound n D g p A ≤ PreparationInput.wordBound B B B B B :=
    Nat.mul_le_mul_left 16 henv
  have hn2 := Nat.pow_le_pow_left hn 2
  have harg : 2 * PreparationInput.wordBound n D g p A + n + n ^ 2 + 5 ≤
      2 * PreparationInput.wordBound B B B B B + B + B ^ 2 + 5 := by omega
  have hr : RecordProduct.admissionWidth n D g p A ≤
      RecordProduct.admissionWidth B B B B B :=
    Nat.add_le_add hw (Nat.mul_le_mul_left 256 (Nat.clog_mono_right 2 harg))
  have hM : CallableProduct.windowSize n (n ^ 2) ≤ CallableProduct.windowSize B (B ^ 2) := by
    unfold CallableProduct.windowSize CallableProduct.sourceWidth
    apply Nat.pow_le_pow_right (by decide)
    exact Nat.mul_le_mul_left 128 (Nat.clog_mono_right 2 (by omega))
  have henv' : RecordWitness.envelope n D g p A ≤ RecordWitness.envelope B B B B B := by
    unfold RecordWitness.envelope
    gcongr
  have hr' : RecordWitness.admissionWidth n D g p A ≤
      RecordWitness.admissionWidth B B B B B := by
    unfold RecordWitness.admissionWidth
    exact Nat.add_le_add_right (max_le_max hr (Nat.clog_mono_right 2 henv')) 3
  have hC : FixedPrime.counterEnvelope n p ≤ FixedPrime.counterEnvelope B B := by
    unfold FixedPrime.counterEnvelope
    gcongr
  exact max_le_max hr' (Nat.add_le_add_right (Nat.clog_mono_right 2 hC) 1)

/-- A word sum bounding every original integer's magnitude guarantees the whole source
admission. This is a numerical theorem; the adapter computes the sum and logarithm itself. -/
theorem source_admission (n D g p total : ℕ) :
    FixedPrime.admissionWidth n D g p total ≤ sourceWidth n D g p total := by
  let B := n + D + g + p + total + 2
  have hm : FixedPrime.admissionWidth n D g p total ≤
      FixedPrime.admissionWidth B B B B B := admission_mono (by omega) (by omega)
    (by omega) (by omega) (by omega)
  have hl := FixedPrime.admissionWidth_le_log (κ := 1) (A := B) (by omega : 1 ≤ B)
    (le_refl B) (le_refl B) (le_refl B) (by simp)
  exact hm.trans (by simpa only [sourceWidth, B, Nat.reduceMul, Nat.reduceAdd] using hl)

/-- The computed source is wide enough for the two-bit signed-kernel extension. -/
theorem sourceWidth_two_lt (n D g p total : ℕ) : 2 < sourceWidth n D g p total := by
  have hc : 1 ≤ Nat.clog 2 (n + D + g + p + total + 4) := Nat.clog_pos
    (by decide) (by omega)
  unfold sourceWidth
  omega

/-- The computed modulus covers the original scalar sum, exponent and native coefficient.
These are original-parameter facts, independent of the physical width or any execution. -/
theorem source_bounds (n D g p total : ℕ) :
    n + D + g + p + total + 4 ≤ windowSize n D g p total ∧
      sourceWidth n D g p total < windowSize n D g p total ∧
      6166 ≤ windowSize n D g p total := by
  have hlog : Nat.clog 2 (n + D + g + p + total + 4) ≤ sourceWidth n D g p total := by
    unfold sourceWidth
    omega
  have hsize : n + D + g + p + total + 4 ≤ windowSize n D g p total :=
    (Nat.le_pow_clog (by decide) _).trans (Nat.pow_le_pow_right (by decide) hlog)
  have hwidth : sourceWidth n D g p total < windowSize n D g p total := Nat.lt_two_pow_self
  have hc : 1 ≤ Nat.clog 2 (n + D + g + p + total + 4) :=
    Nat.clog_pos (by decide) (by omega)
  have h6166 : 6166 ≤ sourceWidth n D g p total := by unfold sourceWidth; omega
  exact ⟨hsize, hwidth, h6166.trans hwidth.le⟩

end Cslib.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime
