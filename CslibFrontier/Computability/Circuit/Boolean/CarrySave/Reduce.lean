/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.CarryLookahead

/-!
# Balanced sums of carry-save pairs

The existing half-split circuit tree reduces any list of carry-save pairs. Its value is their
sum modulo `2 ^ w`, including the empty list. One carry-lookahead addition finishes the result.
These are the arithmetic reductions used by modular multiplication and GSW's selected-row product.

## Main definitions

* `Cslib.Circuits.Boolean.pairWithZero`: put an ordinary word into carry-save form.
* `Cslib.Circuits.Boolean.sumPairs`: reduction followed by logarithmic-depth addition.

## Main results

* `Cslib.Circuits.Boolean.val_eval_sumPairs`: the resulting modular word.

## References

The underlying carry-save construction and source credit are in `Boolean.CarrySave`;
parallel-prefix finishing follows [Ladner and Fischer][LadnerFischer1980].
-/

public section

namespace Cslib.Circuits.Boolean

open BitString

variable {n w : ℕ}

/-- Put an ordinary word into carry-save form, with a shared false gate for the second word. -/
def pairWithZero (C : Circuit signature n w) : Circuit signature n (w + w) :=
  C.append ((Circuit.wiring signature (fun _ : Fin w => (0 : Fin 1))).comp
    (Circuit.oneGate (.const false) Fin.elim0))

/-- Evaluating `pairWithZero C` appends `w` false bits to the output of `C`. -/
@[simp] theorem eval_pairWithZero (C : Circuit signature n w) (x : BitString n) :
    (pairWithZero C).eval interpretation x =
      Fin.append (C.eval interpretation x) (fun _ => false) := by
  simp only [pairWithZero, Circuit.eval_append, Circuit.eval_comp, Circuit.eval_wiring]
  rfl

/-- The carry-save value `pairVal` of `pairWithZero C` equals the unsigned value of `C`. -/
theorem pairVal_eval_pairWithZero (C : Circuit signature n w) (x : BitString n) :
    pairVal ((pairWithZero C).eval interpretation x) =
      (BitString.equivFin w (C.eval interpretation x) : ℕ) := by
  rw [eval_pairWithZero, pairVal_append, val_equivFin_false, Nat.add_zero]

/-- `pairWithZero C` adds one shared constant gate to `C`. -/
@[simp] theorem size_pairWithZero (C : Circuit signature n w) :
    (pairWithZero C).size = C.size + 1 := by
  simp [pairWithZero]

/-- The depth of `pairWithZero C` is at most `max C.depth 1`. -/
theorem depth_pairWithZero_le (C : Circuit signature n w) :
    (pairWithZero C).depth ≤ max C.depth 1 := by
  refine (Circuit.depth_append_le _ _).trans (max_le_max le_rfl ?_)
  exact (Circuit.depth_comp_le _ _).trans (by simp)

/-- Finish a balanced carry-save sum as one unsigned modular word. -/
def sumPairs (n w : ℕ) (cs : List (Circuit signature n (w + w))) : Circuit signature n w :=
  (carryLookaheadAdd w).comp (reducePairs n w cs)

/-- Finishing a carry-save word computes its value modulo `2 ^ w`. -/
theorem val_eval_carryLookaheadAdd_pair (p : BitString (w + w)) :
    (BitString.equivFin w ((carryLookaheadAdd w).eval interpretation p) : ℕ) =
      pairVal p % 2 ^ w := by
  simpa only [append_fstBits_sndBits, pairVal] using
    val_eval_carryLookaheadAdd (fstBits p) (sndBits p)

/-- The final word equals the complete pair sum, reduced only modulo the word width. -/
theorem val_eval_sumPairs (cs : List (Circuit signature n (w + w))) (x : BitString n) :
    (BitString.equivFin w ((sumPairs n w cs).eval interpretation x) : ℕ) =
      (cs.map fun C => pairVal (C.eval interpretation x) % 2 ^ w).sum % 2 ^ w := by
  rw [sumPairs, Circuit.eval_comp, val_eval_carryLookaheadAdd_pair,
    pairVal_eval_reducePairs_mod]

/-- Polynomial gate bound retaining the sizes of the actual input circuits. -/
theorem size_sumPairs_le (cs : List (Circuit signature n (w + w))) :
    (sumPairs n w cs).size ≤
      21 * (w + 1) ^ 2 + 1 + (cs.map Circuit.size).sum + cs.length * (40 * w) := by
  have h₁ := size_carryLookaheadAdd_le w
  have h₂ := size_reducePairs_le cs
  simp only [sumPairs, Circuit.size_comp]
  omega

/-- Logarithmic finishing in addition to the balanced pair-reduction depth. -/
theorem depth_sumPairs_le (cs : List (Circuit signature n (w + w))) {D : ℕ}
    (hD : ∀ C ∈ cs, C.depth ≤ D) :
    (sumPairs n w cs).depth ≤
      8 + 2 * Nat.clog 2 (w + 1) + max D 1 + 12 * Nat.clog 2 cs.length := by
  have h₁ := depth_carryLookaheadAdd_le w
  have h₂ := depth_reducePairs_le cs hD
  exact (Circuit.depth_comp_le _ _).trans (by omega)

end Cslib.Circuits.Boolean
