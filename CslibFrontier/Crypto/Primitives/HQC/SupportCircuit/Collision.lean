/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Comparison
public import CslibFrontier.Computability.Circuit.Boolean.WordConstant
import Cslib.Foundations.Data.Fin.Tuple
import CslibFrontier.Foundations.Data.BitString.Binary

/-!
# Collision correction for support sampling

Each inner-loop step of `SampleSupport2` compares the current candidate with one corrected
later entry and replaces a collision by the current offset. Two existing word comparators and
an AND gate test equality; the existing multiplexer selects the replacement word.

## Main definitions

* `Cslib.Crypto.HQC.collisionStepCircuit`: the source's single collision-correction step.

## Main results

* `Cslib.Crypto.HQC.eval_collisionStepCircuit`: exact word-level behavior.
* `Cslib.Crypto.HQC.size_collisionStepCircuit`: exactly `13 * bits + 6` Boolean gates.

## References

The inner-loop operation is [HQC version 5.1][HQC2026], `SampleSupport2`, p. 19, lines 8–10.
Its circuit construction and costs are original bridges to the existing Boolean compiler.
-/

public section

namespace Cslib.Crypto.HQC

open Circuits Circuits.Boolean BitString

/-- Compare the current and later word; on equality, replace the current word by the low
`bits` bits of the offset. Every constant word, comparator, AND and mux gate is explicit. -/
@[expose] def collisionStepCircuit (bits offset : ℕ) : Circuit signature (bits + bits) bits :=
  (muxCircuit bits).comp
    (((Circuit.oneGate Op.and id).comp
      ((leCircuit bits).append ((leCircuit bits).comp
        (Circuit.wiring signature (Fin.append (Fin.natAdd bits) (Fin.castAdd bits)))))).append
      ((wordConstCircuit (bits + bits) (fun i : Fin bits => offset.testBit i.val)).append
        (Circuit.wiring signature (Fin.castAdd bits))))

/-- The circuit is total even when the offset is too large: its replacement is the low word. -/
theorem eval_collisionStepCircuit (bits offset : ℕ) (a b : BitString bits) :
    (collisionStepCircuit bits offset).eval interpretation (Fin.append a b) =
      if a = b then (fun i => offset.testBit i.val) else a := by
  have hs : Fin.append a b ∘ Fin.append (Fin.natAdd bits) (Fin.castAdd bits) =
      Fin.append b a := by
    rw [Fin.comp_append, Fin.append_comp_natAdd, Fin.append_comp_castAdd]
  rw [collisionStepCircuit, Circuit.eval_comp, Circuit.eval_append, Circuit.eval_comp,
    Circuit.eval_append, eval_leCircuit, Circuit.eval_comp, Circuit.eval_wiring, hs,
    eval_leCircuit, Circuit.eval_append, eval_wordConstCircuit, Circuit.eval_wiring,
    Fin.append_comp_castAdd]
  have he : (Circuit.oneGate Op.and (id : Fin 2 → Fin 2)).eval interpretation
      (Fin.append (fun _ : Fin 1 => decide (equivFin bits a ≤ equivFin bits b))
        (fun _ : Fin 1 => decide (equivFin bits b ≤ equivFin bits a))) =
      fun _ : Fin 1 => decide (a = b) := by
    funext i
    change (decide (equivFin bits a ≤ equivFin bits b) &&
      decide (equivFin bits b ≤ equivFin bits a)) = decide (a = b)
    simp only [← Bool.decide_and, ← le_antisymm_iff, (equivFin bits).injective.eq_iff]
  rw [he, eval_muxCircuit]
  simp only [decide_eq_true_eq]

/-- Cost includes two `5 * bits + 1` comparators, an AND, two shared constant gates and the
`3 * bits + 1` multiplexer. Wiring has no Boolean gate cost. -/
theorem size_collisionStepCircuit (bits offset : ℕ) :
    (collisionStepCircuit bits offset).size = 13 * bits + 6 := by
  simp only [collisionStepCircuit, Circuit.size_comp, Circuit.size_append,
    Circuit.size_oneGate, Circuit.size_wiring, size_leCircuit, size_muxCircuit,
    size_wordConstCircuit]
  omega

end Cslib.Crypto.HQC
