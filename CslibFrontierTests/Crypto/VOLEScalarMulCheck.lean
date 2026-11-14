/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Protocols.VOLE.ScalarMulCheck

/-!
# Scalar-challenge QuickSilver multiplication-check examples

The two-gate examples expose the one-based weights `(chi, chi ^ 2)`, exercise the source-order
masked check with a fresh VOLE coordinate, and show a false batch cancelling at a nonzero scalar
challenge. The final example covers the empty batch.
-/

namespace CslibFrontierTests.Crypto.VOLEScalarMulCheck

open Cslib.Probability Cslib.Crypto.Protocols.VOLE
open scoped BigOperators ENNReal

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private def x5 : Fin 2 → ZMod 5 := ![2, 1]
private def y5 : Fin 2 → ZMod 5 := ![3, 4]
private def z5 : Fin 2 → ZMod 5 := ![1, 4]
private def vx5 : Fin 2 → ZMod 5 := ![1, 2]
private def vy5 : Fin 2 → ZMod 5 := ![2, 3]
private def vz5 : Fin 2 → ZMod 5 := ![4, 0]

-- The source indices are one and two, not zero and one.
example : (fun i : Fin 2 => quickSilverWeight (2 : ZMod 5) i) = ![2, 4] := by decide

private def mask5 : VOLECorrelation (ZMod 5) 1 :=
  voleSample ![3] ![1] 4

-- A nontrivial true batch satisfies the source equation `W = U + V * delta` after masking.
example :
    quickSilverMaskedValue x5 y5 z5 vx5 vy5 vz5 2 mask5.delta (mask5.w 0) =
      (quickSilverMaskedReply x5 y5 vx5 vy5 vz5 2 (mask5.u 0) (mask5.v 0)).1 +
        (quickSilverMaskedReply x5 y5 vx5 vy5 vz5 2 (mask5.u 0) (mask5.v 0)).2 *
          mask5.delta := by
  exact quickSilverMaskedReply_correct x5 y5 z5 vx5 vy5 vz5 2 mask5
    (valid_voleSample _ _ _) (by decide)

private def falseOutput5 : Fin 2 → ZMod 5 := ![-1, 1]

-- Both multiplication claims are false.
example : ∀ i : Fin 2, (0 : ZMod 5) * 0 ≠ falseOutput5 i := by decide

-- Residuals `1, -1` cancel at the nonzero scalar challenge `chi = 1`.
example : ∑ i : Fin 2, quickSilverWeight (1 : ZMod 5) i *
    ((0 : ZMod 5) * 0 - falseOutput5 i) = 0 := by decide

example : (PMF.uniformOfFintype (ZMod 5)).toOuterMeasure
    {chi | ∑ i : Fin 2, quickSilverWeight chi i *
      ((0 : ZMod 5) * 0 - falseOutput5 i) = 0} ≤ 2 / (5 : ℝ≥0∞) := by
  simpa only [ZMod.card, Nat.cast_ofNat] using
    toOuterMeasure_quickSilverWeight_sum_eq_zero_le
      (fun i : Fin 2 => (0 : ZMod 5) * 0 - falseOutput5 i) ⟨0, by decide⟩

-- The sequential source-order reply experiment retains both failure contributions.
example (reply : ZMod 5 → PMF (ZMod 5 × ZMod 5)) :
    (do
      let chi ← PMF.uniformOfFintype (ZMod 5)
      let uv ← reply chi
      let delta ← PMF.uniformOfFintype (ZMod 5)
      return decide (quickSilverMulCheckValue (fun _ : Fin 2 => 0) (fun _ => 0)
        falseOutput5 (fun _ => 0) (fun _ => 0) (fun _ => 0) chi delta =
          uv.1 + uv.2 * delta)).toOuterMeasure {true} ≤ 4 / (5 : ℝ≥0∞) := by
  simpa only [ZMod.card, Nat.cast_ofNat] using
    toOuterMeasure_quickSilverMulCheck_le (fun _ : Fin 2 => (0 : ZMod 5)) (fun _ => 0)
      falseOutput5 (fun _ => 0) (fun _ => 0) (fun _ => 0) reply ⟨0, by decide⟩

-- The empty batch has zero verifier value and zero reply for every challenge and key.
example (chi delta : ZMod 5) :
    quickSilverMulCheckValue (fun _ : Fin 0 => 0) (fun _ => 0) (fun _ => 0)
        (fun _ => 0) (fun _ => 0) (fun _ => 0) chi delta = 0 ∧
      quickSilverMulCheckReply (fun _ : Fin 0 => 0) (fun _ => 0) (fun _ => 0)
        (fun _ => 0) (fun _ => 0) chi = (0, 0) := by
  simp [quickSilverMulCheckValue, quickSilverMulCheckReply]

-- An empty batch cannot contain a false multiplication, whatever source-order reply is used.
example (reply : ZMod 5 → PMF (ZMod 5 × ZMod 5)) :
    (do
      let chi ← PMF.uniformOfFintype (ZMod 5)
      let uv ← reply chi
      let delta ← PMF.uniformOfFintype (ZMod 5)
      return decide ((∃ _ : Fin 0, (0 : ZMod 5) * 0 ≠ 0) ∧
        quickSilverMulCheckValue (fun _ : Fin 0 => 0) (fun _ => 0) (fun _ => 0)
          (fun _ => 0) (fun _ => 0) (fun _ => 0) chi delta =
            uv.1 + uv.2 * delta)).toOuterMeasure {true} = 0 := by
  simp

end CslibFrontierTests.Crypto.VOLEScalarMulCheck
