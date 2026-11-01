/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.CountPrime.Input

/-!
# Original-input physical admission for the complete native counter

A positive ceiling-logarithm threshold depends only on the original side, runtime modulus
and weight bound. Every larger physical width executes the same actual initialized program.
No intermediate fit, padding, table or execution certificate is an input hypothesis.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime

open Cslib.WordRAM

/-- The original-input envelope dominates all native signed arithmetic and address budgets. -/
@[expose] def envelope (n p A : ℕ) : ℕ :=
  addressBudget n p (Nat.clog 2 n) (3 + 3 * (n * n)) 3 (3 + n * n)
    (3 + 2 * (n * n)) + magnitudeBudget p (Nat.clog 2 n) A + 1

/-- Positive sufficient physical width, including both bits required by native signed kernels. -/
@[expose] def admissionWidth (n p A : ℕ) : ℕ := Nat.clog 2 (envelope n p A) + 3

/-- Width-independent word and support envelope for every admitted wider execution. -/
@[expose] def wordBound (n p A : ℕ) : ℕ := 16 * envelope n p A

/-- The sufficient width is positive for every original dimension, including empty matrices. -/
theorem admissionWidth_pos (n p A : ℕ) : 0 < admissionWidth n p A := by
  unfold admissionWidth
  omega

private theorem fits_at_width (n p A : ℕ) :
    GenericRAM.Signed.Fits (Nat.clog 2 (envelope n p A) + 1)
        (magnitudeBudget p (Nat.clog 2 n) A : ℤ) ∧
      Fits (admissionWidth n p A)
        (addressBudget n p (Nat.clog 2 n) (3 + 3 * (n * n)) 3 (3 + n * n)
          (3 + 2 * (n * n))) := by
  let E := envelope n p A
  let k := Nat.clog 2 E
  have hp : E ≤ 2 ^ k := Nat.le_pow_clog (by decide) E
  have hm : magnitudeBudget p (Nat.clog 2 n) A < 2 ^ k :=
    (show magnitudeBudget p (Nat.clog 2 n) A < E by dsimp only [E, envelope]; omega).trans_le hp
  have hb : addressBudget n p (Nat.clog 2 n) (3 + 3 * (n * n)) 3 (3 + n * n)
      (3 + 2 * (n * n)) < 2 ^ k :=
    (show addressBudget n p (Nat.clog 2 n) (3 + 3 * (n * n)) 3 (3 + n * n)
      (3 + 2 * (n * n)) < E by dsimp only [E, envelope]; omega).trans_le hp
  refine ⟨⟨by omega, ?_, ?_⟩, (show Fits k _ from hb).mono (by
    dsimp only [admissionWidth, k, E]; omega)⟩
  · simp only [Nat.add_sub_cancel]
    exact (neg_nonpos.mpr (by positivity)).trans (Int.natCast_nonneg _)
  · simp only [Nat.add_sub_cancel]
    exact_mod_cast hm

/-- Complete initialized structured execution at every admitted width, with original input fit,
exact raw modular count, a bounded actual final state and the caller-memory frame. -/
theorem exec_input {W n p A : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hp : 0 < p)
    (hv : ∀ z ∈ values, z.natAbs ≤ A) (hW : admissionWidth n p A ≤ W) :
    InputFits W (inputWords n p values) ∧
    ∃ y, ExecWithin W entryProgram (.init (inputWords n p values)) y (cost n p + 9) ∧
      y.regs Reg.result = Cslib.Algorithms.ExactTriangle.countZeroMod
        (fun α β : Fin n => values.getD (α.val * n + β.val) 0)
        (fun α β : Fin n => values.getD (n * n + α.val * n + β.val) 0)
        (fun α β : Fin n => values.getD (2 * (n * n) + α.val * n + β.val) 0) p ∧
      y.Bounded W ∧
      ∀ d, d < 3 + 3 * (n * n) ∨ memoryEnd n p (Nat.clog 2 n) (3 + 3 * (n * n)) ≤ d →
        y.mem d = (Data.init (inputWords n p values) : Data 128).mem d := by
  obtain ⟨hmag, haddr⟩ := fits_at_width n p A
  obtain ⟨hi, y, he, result, _, frame⟩ := exec_input_at values hlen hp hv hmag
    (by simpa only [Nat.add_assoc, admissionWidth] using haddr)
  have hwidth : Nat.clog 2 (envelope n p A) + 1 + 2 ≤ W := by
    simpa only [Nat.add_assoc, admissionWidth] using hW
  have noWidth : ¬entryProgram.ReadsWidth := by decide +kernel
  have hew := he.mono_width noWidth hwidth
  have hii := hi.mono hwidth
  exact ⟨hii, y, hew, result, hew.bounded (.init hii), frame⟩

end Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime
