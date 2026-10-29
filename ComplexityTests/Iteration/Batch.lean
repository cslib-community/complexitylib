/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.Iteration.Batch

/-!
# Input-time and batched iteration clients

Input times are evaluated on a two-bit counter, including zero time bits; the shared lookup on
present, absent and duplicated keys; the finishing step without a flagged time; the
checkpoint-free power on the identity; and the input-time and batched theorems on the bit-flip
circuit, including an empty batch and the balanced bounds. Promised batches use a proper invariant
set and a non-invariant singleton, checking both actual outputs and the smaller storage budget.
-/

namespace ComplexityTests.Iteration.Batch

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Circuits.Boolean.Iteration

/-- The one-bit negation circuit. -/
private def flip : Circuit signature 1 1 :=
  ⟨.gate .empty ⟨.not, fun _ => .input 0⟩, fun _ => .gate 0⟩

/-! ### Input times and batches -/

/-- Two-bit increment modulo four, least significant bit first. -/
private def inc (x : BitString 2) : BitString 2 := ![!x 0, x 1 ^^ x 0]

-- Time bits `true, true` (least significant first) encode `3` (`00` becomes `11`); time bits
-- `false, true` encode `2` (`01` becomes `11`); and without time bits the state is returned.
example :
    inputTimeIterate inc 2 ![false, false, true, true] = ![true, true] ∧
    inputTimeIterate inc 2 ![true, false, false, true] = ![true, true] ∧
    inputTimeIterate inc 0 ![true, false] = ![true, false] :=
  ⟨by decide, by decide, (inputTimeIterate_zero inc ![true, false]).trans (by decide)⟩

-- Every input time of the flip, with the fixed-power circuits at `L = 1`.
example (m : ℕ) : ∃ out : Circuit signature (1 + m) 1,
    out.Computes interpretation (inputTimeIterate (flip.eval interpretation) m) ∧
      out.size ≤ m * (40000 * powerBudget 1 1 2 1 + 4) := by
  simpa [flip] using variable_time flip m 1 one_pos (by decide)

-- The shared lookup returns the stored value, all-false for an absent key, and the OR of the
-- values stored under a repeated key; without a flagged time the finished state is the fallback.
example :
    lookupOr ![![true, false], ![false, true]] ![![true], ![false]] ![true, false] = ![true] ∧
    lookupOr ![![true, false], ![false, true]] ![![true], ![false]] ![true, true] = ![false] ∧
    lookupOr ![![true, false], ![true, false]] ![![true, false], ![false, true]]
      ![true, false] = ![true, true] ∧
    finishHit (w := 2) inc 1 ![false, false] ![![true, true], ![true, false]]
      ![false, true] = ![false, true] := by
  decide

-- The identity repeats immediately, so the checkpoint-free power applies at `L = 2`.
example (T : ℕ) (hT : 4 ≤ T) : ∃ out : Circuit signature 1 1,
    (∀ x, out.eval interpretation x = x) ∧ out.size ≤ 40000 * powerBudget 1 0 0 2 := by
  have hid : (Circuit.id signature 1).eval interpretation = id := rfl
  obtain ⟨out, hout, hs⟩ := exists_repeat_power (Circuit.id signature 1) T 2 two_pos (by decide)
    hT
  refine ⟨out, fun x => ?_, by simpa using hs⟩
  rw [hout x ⟨0, 1, by decide, by decide, by simp [hid]⟩, hid, Function.iterate_id]
  rfl

-- Two independent flips share one dictionary, and the empty batch is allowed.
example (c : Circuit signature 2 2) (T : ℕ) :
    (∃ out : Circuit signature (2 * 1) (2 * 1),
      out.Computes interpretation (blockMap (flip.eval interpretation)^[T] 2) ∧
        out.size ≤ 100000 * batchBudget 1 1 2 2 1) ∧
    (∃ out : Circuit signature (0 * 2) (0 * 2),
      out.Computes interpretation (blockMap (c.eval interpretation)^[T] 0) ∧
        out.size ≤ 100000 * batchBudget 2 c.size 4 0 1) := by
  refine ⟨?_, batched_fixed_power c 0 T 1 (by decide) one_pos (by decide)⟩
  simpa [flip] using batched_fixed_power flip 2 T 1 (by decide) one_pos (by decide)

-- Two flips, each with its own time.
example (m : ℕ) : ∃ out : Circuit signature (2 * (1 + m)) (2 * 1),
    out.Computes interpretation (blockMap (inputTimeIterate (flip.eval interpretation) m) 2) ∧
      out.size ≤ m * (100000 * batchBudget 1 1 2 2 1 + 4 * (2 * 1)) := by
  simpa [flip] using batched_variable_time flip 2 m 1 (by decide) one_pos (by decide)

-- The balanced batched bounds.
example (c : Circuit signature 3 3) (T : ℕ) : ∃ out : Circuit signature (2 * 3) (2 * 3),
    out.Computes interpretation (blockMap (c.eval interpretation)^[T] 2) ∧
      (out.size : ℝ) ≤ 300000 * optimizedBatchBudget 3 c.size 8 2 :=
  batched_fixed_power_optimized c 2 T two_pos (by decide)

/-! ### Batches on a promised set of states -/

/-- Preserve the first bit and flip the second. -/
private def flipTail : Circuit signature 2 2 :=
  ⟨.gate .empty ⟨.not, fun _ => .input 1⟩, ![.input 0, .gate 0]⟩

private def leftHalf : Finset (BitString 2) := {![false, false], ![false, true]}

private theorem flipTail_invariant : ∀ x ∈ leftHalf, flipTail.eval interpretation x ∈ leftHalf :=
  by decide

-- Three members share the two-state table. Applying the promised theorem gives an actual
-- output on a mixed batch, and the bound charges two relevant states rather than four.
example : ∃ out : Circuit signature 6 6,
    out.eval interpretation ![false, false, false, true, false, false] =
      ![false, true, false, false, false, true] ∧
    out.size ≤ 16500000 := by
  obtain ⟨out, hout, hs⟩ := batched_fixed_power_on flipTail leftHalf 3 3 1
    flipTail_invariant (by decide) one_pos (by decide)
  refine ⟨out, ?_, by simpa [leftHalf, flipTail, batchBudget] using hs⟩
  have hx : ∀ member : Fin 3,
      directProductInput ![false, false, false, true, false, false] member ∈ leftHalf := by decide
  exact (hout hx).trans (by decide)

-- A single trajectory recovers `powerBudget`; the promise is proper; the improved budget is
-- strictly smaller than the global one; and prefix containment does not assume invariance.
example :
    batchBudget 2 1 leftHalf.card 1 1 = powerBudget 2 1 leftHalf.card 1 ∧
    (¬∀ member : Fin 3,
      directProductInput ![true, false, false, true, false, false] member ∈ leftHalf) ∧
    (batchBudget 2 1 leftHalf.card 3 1 = 165 ∧ batchBudget 2 1 4 3 1 = 219) ∧
    flipTail.eval interpretation ![false, false] ∉
      ({![false, false]} : Finset (BitString 2)) :=
  ⟨batchBudget_one 2 1 leftHalf.card 1, by decide, by decide, by decide⟩

example : ∃ out : Circuit signature 6 6,
    out.eval interpretation ![false, false, false, false, false, false] =
      ![false, true, false, true, false, true] ∧
    out.size ≤ 13800000 := by
  obtain ⟨out, hout, hs⟩ := batched_fixed_power_on_prefixes flipTail {![false, false]} 3 3 1
    (by decide) one_pos (by decide)
  refine ⟨out, ?_, by simpa [flipTail, batchBudget] using hs⟩
  have hx : ∀ member : Fin 3, ∀ i : Fin 1,
      (flipTail.eval interpretation)^[i.val]
        (directProductInput ![false, false, false, false, false, false] member) ∈
          ({![false, false]} : Finset (BitString 2)) := by decide
  exact (hout hx).trans (by decide)

-- The optimized theorem keeps the same proper input domain.
example (T : ℕ) : ∃ out : Circuit signature 6 6,
    out.ComputesOn interpretation
      {x | ∀ member : Fin 3, directProductInput x member ∈ leftHalf}
      (blockMap (flipTail.eval interpretation)^[T] 3) ∧
    (out.size : ℝ) ≤ 300000 * optimizedBatchBudget 2 1 2 3 := by
  simpa [leftHalf, flipTail] using
    batched_fixed_power_on_optimized flipTail leftHalf 3 T flipTail_invariant
      (by decide) (by decide)

end ComplexityTests.Iteration.Batch
