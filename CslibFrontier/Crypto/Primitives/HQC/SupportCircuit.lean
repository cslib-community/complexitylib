/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Modular.Multiply
public import CslibFrontier.Computability.Circuit.Boolean.WordConstant
public import CslibFrontier.Crypto.Primitives.HQC.SupportSampling
import CslibFrontier.Foundations.Data.BitString.Prefix
import CslibFrontier.Foundations.Data.BitString.Binary

/-!
# Boolean circuits for HQC support sampling

The candidate circuit implements the multiply-high expression in `SampleSupport2` using the
existing modular multiplier and carry-lookahead adder. It widens intermediate products before
selecting the high bits, so its correctness theorem requires no overflow approximation.

## Main definitions

* `Cslib.Crypto.HQC.candidateCircuit`: one bounded-word candidate at a specified offset.

## Main results

* `Cslib.Crypto.HQC.val_eval_candidateCircuit`: exact candidate value.
* `Cslib.Crypto.HQC.size_candidateCircuit`: multiplier, adder and exactly six constant gates.
* `Cslib.Crypto.HQC.size_candidateCircuit_le`: a construction-derived Boolean gate bound.

## References

The candidate formula is [HQC version 5.1][HQC2026], `SampleSupport2`, p. 19, line 5.
The circuit construction and its costs are original bridges to the existing Boolean compiler.
-/

public section

namespace Cslib.Crypto.HQC

open Circuits Circuits.Boolean BitString

/-- Compute one source candidate from its fair input word. Constants and zero padding use the
existing shared two-gate constant-word circuit. The total circuit truncates to `bits` outputs. -/
@[expose] def candidateCircuit (width bits n offset : ℕ) : Circuit signature width bits :=
  (carryLookaheadAdd bits).comp
    (((Circuit.wiring signature (Fin.natAdd width : Fin bits → Fin (width + bits))).comp
      ((Modular.multiply (width + bits)).comp
        (((Circuit.id signature width).append
          (wordConstCircuit width (fun _ : Fin bits => false))).append
          (wordConstCircuit width (fun i : Fin (width + bits) =>
            (n - offset).testBit i.val))))).append
      (wordConstCircuit width (fun i : Fin bits => offset.testBit i.val)))

/-- With a wide enough output word and a valid shrinking interval, the circuit computes the
source's exact multiply-high candidate, not a modular-reduction approximation. -/
theorem val_eval_candidateCircuit {width bits n offset : ℕ} (hoff : offset < n)
    (hn : n < 2 ^ bits) (x : BitString width) :
    (equivFin bits ((candidateCircuit width bits n offset).eval interpretation x) : ℕ) =
      offset + (equivFin width x : ℕ) * (n - offset) / 2 ^ width := by
  have hpad : Fin.append x (fun _ : Fin bits => false) =
      zeroExtend (d' := width + bits) x := by
    funext i
    cases i using Fin.addCases with
    | left i => simp [zeroExtend, i.isLt]
    | right i => simp [zeroExtend, Nat.not_lt.mpr (Nat.le_add_right width i.val)]
  have hwide : n < 2 ^ (width + bits) :=
    hn.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have hc (r a : ℕ) : (equivFin r (fun i : Fin r => a.testBit i.val) : ℕ) = a % 2 ^ r := by
    rw [val_equivFin_eq_div_mod_of_testBit (s := 0) (N := a) (by simp),
      Nat.pow_zero, Nat.div_one]
  have hlow := Nat.mul_div_lt_of_lt (M := 2 ^ width) (d := n - offset)
    (by positivity) (by omega) (equivFin width x).isLt
  have hmul : (equivFin width x : ℕ) * (n - offset) < 2 ^ (width + bits) := by
    rw [pow_add]
    exact Nat.mul_lt_mul'' (equivFin width x).isLt ((Nat.sub_le n offset).trans_lt hn)
  let product := (Modular.multiply (width + bits)).eval interpretation
    (Fin.append (zeroExtend (d' := width + bits) x)
      (fun i : Fin (width + bits) => (n - offset).testBit i.val))
  have hp : (equivFin (width + bits) product : ℕ) =
      (equivFin width x : ℕ) * (n - offset) := by
    dsimp only [product]
    rw [Modular.val_eval_multiply, val_equivFin_zeroExtend_of_ge (by omega), hc,
      Nat.mod_eq_of_lt ((Nat.sub_le n offset).trans_lt hwide), Nat.mod_eq_of_lt hmul]
  have hh : (equivFin bits (product ∘ Fin.natAdd width) : ℕ) =
      (equivFin width x : ℕ) * (n - offset) / 2 ^ width := by
    simp only [Function.comp_def]
    rw [val_equivFin_eq_div_mod_of_testBit (s := width) (N := equivFin (width + bits) product)
      (fun i => (testBit_equivFin product (Fin.natAdd width i)).symm), hp,
      Nat.mod_eq_of_lt (hlow.trans ((Nat.sub_le n offset).trans_lt hn))]
  simp only [candidateCircuit, Circuit.eval_comp, Circuit.eval_append, eval_wordConstCircuit,
    Circuit.id, Circuit.eval_wiring, Function.comp_id, hpad]
  rw [val_eval_carryLookaheadAdd, hh, hc, Nat.mod_eq_of_lt (hoff.trans hn),
    Nat.mod_eq_of_lt (show (equivFin width x : ℕ) * (n - offset) / 2 ^ width + offset <
      2 ^ bits by omega)]
  omega

/-- There are three two-gate constant words, plus the existing multiplier and adder.
Output selections and input copies are free wires in the Boolean circuit model. -/
theorem size_candidateCircuit (width bits n offset : ℕ) :
    (candidateCircuit width bits n offset).size =
      (Modular.multiply (width + bits)).size + (carryLookaheadAdd bits).size + 6 := by
  simp only [candidateCircuit, Circuit.size_comp, Circuit.size_append, Circuit.size_wiring,
    size_wordConstCircuit, Circuit.id]
  omega

/-- Every constant, multiplier and adder gate is charged; output selections are free wires. -/
theorem size_candidateCircuit_le (width bits n offset : ℕ) :
    (candidateCircuit width bits n offset).size ≤
      63 * (width + bits + 1) ^ 2 + 21 * (bits + 1) ^ 2 + 6 := by
  rw [size_candidateCircuit]
  have := Modular.size_multiply_le (width + bits)
  have := size_carryLookaheadAdd_le bits
  omega

end Cslib.Crypto.HQC
