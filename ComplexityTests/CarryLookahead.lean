/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.CarryLookahead.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Carry-lookahead arithmetic and uniform generation clients

The examples distinguish significance order, preserve carry-in at width zero, exercise a
non-power-of-two propagation chain, and finish an existing carry-save reduction. Runtime clients
generate complete binary circuit codes at growing widths and at arbitrary binary scan distances.
-/

namespace ComplexityTests.CarryLookahead

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open Turing.MultiTapeTM ComputableInPolyTime

-- At width zero the carry is the sole output, whereas the modular output is empty.
example (c : Bool) :
    (carryLookahead 0).eval interpretation (fun _ => c) = fun _ => c := by
  funext i
  fin_cases i
  cases c <;> rfl

example : (carryLookaheadAdd 0).eval interpretation Fin.elim0 = Fin.elim0 := by
  funext i
  exact i.elim0

-- Low generate/high kill and low kill/high generate must not be interchanged.
example : (carryLookahead 2).eval interpretation
    (Fin.append (Fin.append ![true, false] ![true, false]) (fun _ => false)) =
      ![false, true, false] := by
  apply (BitString.equivFin 3).injective
  apply Fin.ext
  rw [val_eval_carryLookahead]
  decide

example : (carryLookahead 2).eval interpretation
    (Fin.append (Fin.append ![false, true] ![false, true]) (fun _ => false)) =
      ![false, false, true] := by
  apply (BitString.equivFin 3).injective
  apply Fin.ext
  rw [val_eval_carryLookahead]
  decide

-- Five is not a power of two: carry-in crosses all five positions and becomes the output carry.
example : (carryLookahead 5).eval interpretation
    (Fin.append (Fin.append (fun _ => true) (fun _ => false)) (fun _ => true)) =
      ![false, false, false, false, false, true] := by
  apply (BitString.equivFin 6).injective
  apply Fin.ext
  rw [val_eval_carryLookahead]
  decide

-- The same overflow is discarded by the modular interface.
example : (BitString.equivFin 5 ((carryLookaheadAdd 5).eval interpretation
    (Fin.append (fun _ => true) ![true, false, false, false, false])) : ℕ) = 0 := by
  rw [val_eval_carryLookaheadAdd]
  decide

-- An inactive round retains every summary even at a large binary-encoded distance.
example : (Cslib.Circuits.Boolean.CarryLookahead.step 3 (2 ^ 100)).eval interpretation
    ![true, false, true, false, true, false] = ![true, false, true, false, true, false] := by
  funext i
  fin_cases i <;>
    simp only [Cslib.Circuits.Boolean.CarryLookahead.step,
      Circuit.eval_append, Circuit.eval_pi, Formula.eval_toCircuit,
      Formula.eval_or, Formula.eval_and, Formula.eval_input,
      Cslib.Circuits.Boolean.CarryLookahead.generateFormula,
      Cslib.Circuits.Boolean.CarryLookahead.propagateFormula,
      Cslib.Circuits.Boolean.CarryLookahead.neighbour,
      Formula.eval_or, Formula.eval_and, Formula.eval_input] <;> decide

-- The replacement finishes an existing 4-to-2 carry-save circuit, with every input arbitrary.
example (w : ℕ) (p q : BitString (w + w)) :
    pairVal (((carryLookaheadFinish w).comp (csa4to2 w)).eval interpretation
      (Fin.append p q)) % 2 ^ w = (pairVal p + pairVal q) % 2 ^ w ∧
    BitString.sndBits (((carryLookaheadFinish w).comp (csa4to2 w)).eval interpretation
      (Fin.append p q)) = (fun _ => false) := by
  exact ⟨pairVal_eval_carryLookaheadFinish_csa4to2_mod p q,
    by rw [Circuit.eval_comp]; exact sndBits_eval_carryLookaheadFinish _⟩

example (w : ℕ) : (carryLookaheadAdd w).depth ≤ 8 * (Nat.clog 2 (w + 1) + 1) ∧
    (carryLookaheadAdd w).size ≤ 21 * (w + 1) ^ 2 :=
  ⟨depth_carryLookaheadAdd_le_log w, size_carryLookaheadAdd_le w⟩

-- The actual generated code is accepted by the ordinary checked circuit decoder and has
-- `w + 1` outputs.
example (w : ℕ) :
    Circuit.ofCode (σ := signature) (w + w + 1) (w + 1) (carryLookahead w).code =
      some (carryLookahead w) ∧
    (carryLookahead w).code.2.length = w + 1 :=
  ⟨Circuit.ofCode_code _, by simp [Circuit.code]⟩

/-- A single native algorithm generates full adder codes at an unbounded computed width. -/
theorem growingWidth_polynomialTime :
    ComputableInPolyTime (fun k : ℕ => (carryLookahead (2 * k + 1)).code)
      encUnary encCode :=
  computableInPolyTime_carryLookahead.comp (by fun_prop)

/-- The modular and carry-save finishing generators are also uniform in the unary width. -/
theorem modularAndFinish_polynomialTime :
    ComputableInPolyTime (fun w => ((carryLookaheadAdd w).code,
      (carryLookaheadFinish w).code)) encUnary (encPair encCode encCode) :=
  computableInPolyTime_carryLookaheadAdd.prod
    computableInPolyTime_carryLookaheadFinish

/-- Distances are binary and need not be polynomially bounded as natural numbers. -/
theorem arbitraryDistance_polynomialTime :
    ComputableInPolyTime
      (fun p : ℕ × ℕ => Cslib.Circuits.Boolean.CarryLookahead.stepCode p.1 p.2)
      (encPair encUnary encNat) encCode :=
  Cslib.Circuits.Boolean.CarryLookahead.computableInPolyTime_stepCode
    (fst _ _) (snd _ _)

end ComplexityTests.CarryLookahead
