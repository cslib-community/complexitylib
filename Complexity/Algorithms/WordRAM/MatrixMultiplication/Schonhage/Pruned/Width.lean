/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Flat
public import Mathlib.Data.Nat.Log

/-!
# Sufficient physical width from original pruned-query inputs

## Main definitions

* `PrunedQuery.admissionWidth`: three bits beyond the binary ceiling logarithm of the combined
  original magnitude and address budgets.

## Main results

* `PrunedQuery.runs_wide`: at every admitted physical width, the same finite program starts
  from actual initialized input, returns every requested result and halts within the charged bound.

Input fit is a conclusion, including both scalar headers and the machine's length word. This
component's threshold is logarithmic in its explicit budgets. Relating the encoding depth, query
count and magnitudes to a whole 3SUM input is separate composition work under #1394.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

open Cslib.WordRAM Cslib.WordRAM.Signed
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- A positive threshold for the physical target width, computed from original parameters.
The code does not inspect this number or the machine width. -/
def admissionWidth (L Q A B : ℕ) : ℕ :=
  Nat.clog 2 (magnitudeBound L A B + addressBound L Q + 1) + 3

/-- The physical threshold is nonzero even for empty inputs and zero operands. -/
theorem admissionWidth_pos (L Q A B : ℕ) : 0 < admissionWidth L Q A B := by
  unfold admissionWidth
  omega

/-- Mathlib's ceiling logarithm derives both actual address-word fit and the signed source
envelope, retaining the two extra bits charged by the existing signed arithmetic kernels. -/
theorem admission_bounds {W L Q A B : ℕ} (hW : admissionWidth L Q A B ≤ W) :
    0 < W - 2 ∧ magnitudeBound L A B < 2 ^ ((W - 2) - 1) ∧ Fits W (addressBound L Q) := by
  have hlog := Nat.le_pow_clog (by decide : 1 < (2 : ℕ))
    (magnitudeBound L A B + addressBound L Q + 1)
  have hs : Nat.clog 2 (magnitudeBound L A B + addressBound L Q + 1) ≤ (W - 2) - 1 := by
    unfold admissionWidth at hW
    omega
  have hpower := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hs
  refine ⟨by unfold admissionWidth at hW; omega, by omega, ?_⟩
  change addressBound L Q < 2 ^ W
  have hpower' := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega :
    Nat.clog 2 (magnitudeBound L A B + addressBound L Q + 1) ≤ W)
  omega

/-- A complete initialized run at every sufficiently wide physical width, with guaranteed input
fit, a shared pre-halt memory witness, charged halt, all output values and outside preservation. -/
theorem runs_wide {W L A B : ℕ} (a b : Fin (10 ^ L) → ℤ)
    (qs : List (Fin (10 ^ L))) (ha : ∀ v, |a v| ≤ (A : ℤ)) (hb : ∀ v, |b v| ≤ (B : ℤ))
    (hW : admissionWidth L qs.length A B ≤ W) :
    InputFits W (input L a b qs) ∧
    ∃ y n, n ≤ timeBound qs ∧
      Runs W (program.program output) (State.init (input L a b qs)) ⟨program.size, y⟩ n ∧
      Executes W (program.program output) (State.init (input L a b qs))
        (outputBase L qs.length) (n + 1) ∧ y.Bounded W ∧
      (∀ i : Fin qs.length, y.mem (outputBase L qs.length + i.val) = encode
        (Pruned.result L (fun v => a (Encoding.leafIndex v))
          (fun v => b (Encoding.leafIndex v)) (requested qs) (queryAt (qs.get i)))) ∧
      (∀ c, ¬(outputBase L qs.length ≤ c ∧ c < memoryEnd L qs.length) →
        y.mem c = (State.init (input L a b qs) : State registers).data.mem c) := by
  obtain ⟨hw, hm, ha'⟩ := admission_bounds hW
  have htwo : W - 2 + 2 = W := by unfold admissionWidth at hW; omega
  have h := runs hw a b qs ha hb hm (by simpa only [htwo] using ha')
  simpa only [htwo] using h

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery
