/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Primitives.HQC.SupportCircuit.PolyTime
public import CslibFrontier.Computability.Circuit.Quantum.Reversible.Resources
import CslibFrontier.Foundations.Data.BitString.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Mathlib.Data.Fin.VecNotation

/-! Concrete native generation, nonconstant reversible execution, and candidate boundary cases. -/

public section

namespace CslibFrontierTests.HQCSupportCircuit

open Cslib Cslib.Crypto.HQC Cslib.Circuits Cslib.Circuits.Boolean Cslib.Quantum
open Turing.MultiTapeTM ComputableInPolyTime

private def candidateBit (width : ℕ) : Circuits.Circuit signature width 1 :=
  (Circuits.Circuit.wiring signature (fun _ : Fin 1 => (0 : Fin 3))).comp
    (candidateCircuit width 3 5 1)

private theorem candidateBit_polyTime :
    ComputableInPolyTime (fun width => (candidateBit width).code) encUnary encCode := by
  have h := computableInPolyTime_compCode unary_to_binary
    (const (Circuits.Circuit.wiring signature (fun _ : Fin 1 => (0 : Fin 3))).code)
    (computableInPolyTime_candidateCircuit id' (const 3) (const 5) (const 1))
  simpa only [candidateBit, compCode_code] using h

def candidateFamily : UniformCircuitFamily :=
  .ofBooleanCircuits candidateBit candidateBit_polyTime

private theorem candidateFamily_accept (x : List Bool) :
    candidateFamily.acceptProb x =
      if (1 + (BitString.equivFin x.length (fun i => x[i]) : ℕ) * 4 / 2 ^ x.length).testBit 0
      then 1 else 0 := by
  rw [candidateFamily, UniformCircuitFamily.acceptProb_ofBooleanCircuits]
  simp only [candidateBit, Circuits.Circuit.eval_comp, Circuits.Circuit.eval_wiring,
    Function.comp_apply]
  rw [← BitString.testBit_equivFin
    ((candidateCircuit x.length 3 5 1).eval interpretation (fun i => x[i])) (0 : Fin 3),
    val_eval_candidateCircuit (by decide : 1 < 5) (by decide : 5 < 2 ^ 3)]
  rfl

-- Actual compiled quantum execution distinguishes two different fair-word inputs.
example : candidateFamily.acceptProb [false, false] = 1 := by
  rw [candidateFamily_accept]
  norm_num [BitString.val_equivFin_eq_sum, Fin.sum_univ_two]
  decide

example : candidateFamily.acceptProb [true, false] = 0 := by
  rw [candidateFamily_accept]
  norm_num [BitString.val_equivFin_eq_sum, Fin.sum_univ_two]
  decide

-- The first shrinking interval can have three elements, so this is not dyadic reduction.
example : (BitString.equivFin 2 ((candidateCircuit 2 2 3 0).eval interpretation ![true, true]) : ℕ)
    = 2 := by
  rw [val_eval_candidateCircuit (by decide) (by decide)]
  norm_num [BitString.val_equivFin_eq_sum, Fin.sum_univ_succ]

-- A zero-bit random word gives the lower endpoint, without abort or an uncharged random draw.
example : (BitString.equivFin 3 ((candidateCircuit 0 3 5 2).eval interpretation Fin.elim0) : ℕ)
    = 2 := by
  rw [val_eval_candidateCircuit (by decide) (by decide)]
  norm_num [BitString.val_equivFin_eq_sum]

-- Raw generation remains total for invalid intervals and empty outputs.
example : (candidateCode 0 0 0 1).2 = [] := by decide

example (width : ℕ) : (candidateBit width).size ≤
    63 * (width + 4) ^ 2 + 342 := by
  have h := size_candidateCircuit_le width 3 5 1
  simpa [candidateBit, Nat.add_assoc] using h

end CslibFrontierTests.HQCSupportCircuit
