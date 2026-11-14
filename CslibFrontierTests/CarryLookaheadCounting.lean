/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarryLookaheadCounting

/-!
The complete native machine, including its finishing adder, handles both an empty count and a
positive count with a binary carry. One finite machine answers both bits and both claimed values;
its actual initial control state and its full all-branch clock are used throughout.
-/

namespace CslibFrontierTests.CarryLookaheadCounting

open Turing Turing.MultiTapeTM Turing.MultiTapeATM
open Cslib Cslib.Circuits.Boolean.CarrySaveQuery
open Turing.MultiTapeATM.CarryLookaheadCounting

/-- Shared empty/positive count fixture for prepared and raw-parameter machine regressions. -/
theorem count_bits (filled : Bool) (bit : Fin 2) :
    Counting.count (if filled then 2 else 0) 2 (fun _ => true) bit =
      (filled && (bit == 1)) := by
  have hbound : (if filled then 2 else 0) < 2 ^ 2 := by cases filled <;> decide
  have hv : (BitString.equivFin 2
      (Counting.count (if filled then 2 else 0) 2 (fun _ => true)) : ℕ) =
        if filled then 2 else 0 := by
    simpa using Counting.val_count_eq (if filled then 2 else 0) 2 (fun _ => true) hbound
  have hword : Counting.count (if filled then 2 else 0) 2 (fun _ => true) = ![false, filled] := by
    apply (BitString.equivFin 2).injective
    apply Fin.ext
    rw [hv]
    cases filled <;> decide
  rw [hword]
  fin_cases bit <;> cases filled <;> rfl

-- The positive instance counts two true leaves, so bit zero is false and bit one is true.
-- The empty instance rejects a true claim for either bit using the same finite native machine.
example : ∃ (k r q : ℕ) (S : Type) (_ : Finite S)
    (atm : MultiTapeATM (CarryLookaheadCountingLayout.size k r q) Bool S)
    (c d cRoot dRoot : ℕ),
    ∀ (input : List Bool) (filled : Bool) (bit : Fin 2) (claim : Bool),
      let n := if filled then 2 else 0
      let start := (initial k r q input [] n 2 bit.val claim).withState
        (some atm.toPTM.initial)
      atm.HaltsWithin (clock c d cRoot dRoot [] n 2) start ∧
        (atm.AcceptsWithin (clock c d cRoot dRoot [] n 2) start ↔
          (filled && (bit == 1)) = claim) := by
  obtain ⟨k, r, q, S, hS, atm, c, d, cRoot, dRoot, h⟩ :=
    exists_evaluator (fun _ => true) (ComputableInPolyTime.const true)
  refine ⟨k, r, q, S, hS, atm, c, d, cRoot, dRoot, ?_⟩
  intro input filled bit claim
  have hrun := h input [] (if filled then 2 else 0) 2 bit claim
  refine ⟨hrun.1, hrun.2.trans ?_⟩
  rw [count_bits]

end CslibFrontierTests.CarryLookaheadCounting
