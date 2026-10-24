/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.CarryLookahead

/-!
# Modular subtraction with carry lookahead

Subtract by complementing the second word and supplying an incoming carry of one. The output
discards the final carry, so underflow wraps modulo `2 ^ w` instead of truncated subtraction.

## Main definitions

* `Cslib.Circuits.Boolean.Modular.subtract`: the modular subtraction circuit.

## Main results

* `Cslib.Circuits.Boolean.Modular.val_eval_subtract`: exact modular subtraction on all words.
* `Cslib.Circuits.Boolean.Modular.depth_subtract_le`: depth at most `8 + 2 * clog 2 (w + 1)`.
* `Cslib.Circuits.Boolean.Modular.size_subtract_le`: size at most `21 * (w + 1) ^ 2`.

## References

Parallel-prefix finishing follows [Ladner and Fischer][LadnerFischer1980].
-/

public section

namespace Cslib.Circuits.Boolean.Modular

open BitString

variable {w : ℕ}

/-- Keep the first word, complement the second word in parallel, and append a true carry. -/
private def subtractInputs (w : ℕ) : Circuit signature (w + w) (w + w + 1) :=
  ((Circuit.wiring signature (Fin.castAdd w)).append
    (Circuit.pi fun i : Fin w => (Formula.input (Fin.natAdd w i)).not.toCircuit)).append
      (Circuit.oneGate (.const true) Fin.elim0)

@[simp] private theorem eval_subtractInputs (a b : BitString w) :
    (subtractInputs w).eval interpretation (Fin.append a b) =
      Fin.append (Fin.append a (fun i => !b i)) (fun _ => true) := by
  simp only [subtractInputs, Circuit.eval_append, Circuit.eval_wiring, Circuit.eval_pi,
    Formula.eval_toCircuit, Formula.eval_not, Formula.eval_input, Fin.append_right]
  congr 2
  funext i
  exact Fin.append_left a b i

@[simp] private theorem size_subtractInputs (w : ℕ) : (subtractInputs w).size = w + 1 := by
  simp [subtractInputs]

private theorem depth_subtractInputs_le (w : ℕ) : (subtractInputs w).depth ≤ 1 := by
  apply (Circuit.depth_append_le _ _).trans
  apply max_le
  · apply (Circuit.depth_append_le _ _).trans
    apply max_le (by simp)
    apply Circuit.depth_pi_le
    intro i
    exact (Formula.depth_toCircuit_le _).trans (by simp)
  · simp

/-- Discard the carry-out after adding the first word, the second word's complement and one. -/
def subtract (w : ℕ) : Circuit signature (w + w) w :=
  (Circuit.wiring signature (fun i : Fin w => i.castSucc)).comp
    ((carryLookahead w).comp (subtractInputs w))

private theorem val_not (b : BitString w) :
    (BitString.equivFin w (fun i => !b i) : ℕ) = 2 ^ w - 1 - (BitString.equivFin w b : ℕ) := by
  have h : word (fun i => !b i) = ~~~word b := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [getLsbD_word _ ⟨i, hi⟩, BitVec.getLsbD_not, hi, decide_true, Bool.true_and]
  have hv := congrArg BitVec.toNat h
  simpa only [toNat_word_eq_equivFin, BitVec.toNat_not] using hv

/-- Modular subtraction, expressed without a truncated natural subtraction of the inputs. -/
theorem val_eval_subtract (a b : BitString w) :
    (BitString.equivFin w ((subtract w).eval interpretation (Fin.append a b)) : ℕ) =
      (2 ^ w - (BitString.equivFin w b : ℕ) + (BitString.equivFin w a : ℕ)) % 2 ^ w := by
  have h := val_eval_carryLookahead a (fun i => !b i) true
  rw [BitString.val_equivFin_succ] at h
  have hm := congrArg (· % 2 ^ w) h
  rw [Nat.add_mul_mod_self_right] at hm
  have he : (subtract w).eval interpretation (Fin.append a b) =
      Fin.init ((carryLookahead w).eval interpretation
        (Fin.append (Fin.append a (fun i => !b i)) (fun _ => true))) := by
    simp only [subtract, Circuit.eval_comp, Circuit.eval_wiring, eval_subtractInputs]
    rfl
  rw [he]
  have hb := (BitString.equivFin w b).isLt
  rw [val_not, Bool.toNat_true] at hm
  have hv : (BitString.equivFin w a : ℕ) +
      (2 ^ w - 1 - (BitString.equivFin w b : ℕ)) + 1 =
        2 ^ w - (BitString.equivFin w b : ℕ) + (BitString.equivFin w a : ℕ) := by omega
  rw [hv] at hm
  exact (Nat.mod_eq_of_lt (BitString.equivFin w _).isLt).symm.trans hm

/-- The depth of `subtract w` is at most `8 + 2 * Nat.clog 2 (w + 1)`. -/
theorem depth_subtract_le (w : ℕ) :
    (subtract w).depth ≤ 8 + 2 * Nat.clog 2 (w + 1) := by
  have h := (Circuit.depth_comp_le (carryLookahead w) (subtractInputs w)).trans
    (Nat.add_le_add (depth_carryLookahead_le w) (depth_subtractInputs_le w))
  apply (Circuit.depth_comp_le _ _).trans
  simp only [Circuit.depth_wiring, zero_add]
  omega

/-- The size of `subtract w` is at most `21 * (w + 1) ^ 2`. -/
theorem size_subtract_le (w : ℕ) : (subtract w).size ≤ 21 * (w + 1) ^ 2 := by
  have h := size_carryLookahead_le w
  simp only [subtract, Circuit.size_comp, Circuit.size_wiring, size_subtractInputs]
  nlinarith

end Cslib.Circuits.Boolean.Modular
