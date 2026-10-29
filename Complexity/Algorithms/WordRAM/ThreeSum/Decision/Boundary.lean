/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.Decision.Registers

/-!
# Exact ordinary 3SUM boundary verdicts

Inputs of lengths zero, one and two cannot contain three distinct positions, even when values
repeat. The actual native controller returns false before preprocessing on precisely this
branch. This is a final-verdict optimization, not an assertion about the instance catalogue.

## Main results

* `not_hasSolution_of_length_lt_three`: the existing distinct-position predicate is false.
* `exec_small`: the actual finite controller executes the false branch in six instructions.

These boundary and native execution proofs are original.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Decision

open Cslib.WordRAM

/-- Three distinct input positions require at least three entries. -/
theorem not_hasSolution_of_length_lt_three {n : ℕ} (x : Fin n → ℤ) (hn : n < 3) :
    ¬Cslib.Algorithms.ThreeSum.HasSolution x := by
  rintro ⟨i, j, k, hij, hjk, hik, _⟩
  have hi := i.isLt
  have hj := j.isLt
  have hk := k.isLt
  have hij' : i.val ≠ j.val := fun h => hij (Fin.ext h)
  have hjk' : j.val ≠ k.val := fun h => hjk (Fin.ext h)
  have hik' : i.val ≠ k.val := fun h => hik (Fin.ext h)
  omega

/-- The length header and constants are read by actual native instructions. -/
theorem exec_readLength {w : ℕ} (x : Data 16) (h3 : Fits w 3) :
    let y := x.set address 0 |>.set inputLength (x.mem 0) |>.set three 3 |>.set answer 0
    ExecWithin w readLength x y 4 := by
  dsimp only
  ram_eval [readLength, address, inputLength, three, answer, h3, Fin.mk.injEq]

/-- Every admitted empty, singleton or two-entry input follows the actual false-verdict path. -/
theorem exec_small {κ w r : ℕ} (input : List ℤ) (c : Host.Callee r)
    (hn : input.length < 3) (h3 : Fits w 3) :
    ∃ y, ExecWithin w (program κ c) (Data.init (input.map Signed.encode)) y 6 ∧
      y.regs (controllerRegisters r answer) = 0 ∧
      ¬Cslib.Algorithms.ThreeSum.HasSolution (fun i : Fin input.length => input[i]) := by
  let x : Data (registerCount r) := Data.init (input.map Signed.encode)
  let a := (x.comap (controllerRegisters r)).set address 0
    |>.set inputLength input.length |>.set three 3 |>.set answer 0
  let y := a.extend (controllerRegisters r) x
  have hr : ExecWithin w (readLength.rename (controllerRegisters r)) x y 4 := by
    apply ExecWithin.rename (controller_injective r)
    simpa only [Data.comap_mem, x, Data.init_mem_zero, List.length_map] using
      exec_readLength (x.comap (controllerRegisters r)) h3
  have ha : y.regs (controllerRegisters r answer) = 0 := by
    rw [extend_controller]
    simp +decide [a, answer, three, inputLength, address]
  have hlen : y.regs (controllerRegisters r inputLength) = input.length := by
    rw [extend_controller]
    simp +decide [a, answer, three, inputLength, address]
  have ht : y.regs (controllerRegisters r three) = 3 := by
    rw [extend_controller]
    simp +decide [a, answer, three]
  have hcopy : ExecWithin (B := .standard) w
      (.op (.copy (controllerRegisters r answer) (controllerRegisters r answer))) y y 1 := by
    have hself : y.set (controllerRegisters r answer) (y.regs (controllerRegisters r answer)) =
        y := by ext i <;> simp [Data.set]
    simpa only [hself] using (ExecWithin.copy (B := .standard) (w := w)
      (x := y) (d := controllerRegisters r answer) (s := controllerRegisters r answer))
  refine ⟨y, ?_, ha, not_hasSolution_of_length_lt_three _ hn⟩
  have he := hr.seq (hcopy.branch_pos (neg := large κ c) (show
      (Cond.lt (controllerRegisters r inputLength) (controllerRegisters r three)).Holds y by
    simpa only [Cond.holds_lt, hlen, ht] using hn))
  simpa only [program] using he

end Cslib.Algorithms.WordRAM.ThreeSum.Decision
