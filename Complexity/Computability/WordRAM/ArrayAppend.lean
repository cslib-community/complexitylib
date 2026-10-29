/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Allocation
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Appending one word to a realized memory block

## Main results

* `Block.Realizes.snoc`: the actual one-cell memory update realizes `Fin.snoc` of the prior
  finite array. This is a memory identity; a caller must separately charge its store instruction.

This narrow topic module keeps the `Fin.snoc` dependency and append-specific proof out of
`Allocation`. Clients of core allocation then avoid an interface change and rebuild when the
append API changes; consumers import this module alongside `Block.Realizes.update` as needed.
-/

@[expose] public section

namespace Cslib.WordRAM.Block

/-- Appending a value at the first cell after an array realizes the extended finite function. -/
theorem Realizes.snoc {base n : ℕ} {mem : ℕ → ℕ} {v : Fin n → ℕ}
    (h : (Block.mk base n).Realizes mem v) (a : ℕ) :
    (Block.mk base (n + 1)).Realizes (Function.update mem (base + n) a) (Fin.snoc v a) := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [read]
  · have hne : base + j.val ≠ base + n := by have := j.isLt; omega
    simpa only [read, Fin.val_castSucc, Function.update_of_ne hne, Fin.snoc_castSucc] using h j

end Cslib.WordRAM.Block
