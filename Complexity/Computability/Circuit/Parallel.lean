/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Cslib.Computability.Circuit.Simulation
import Complexity.Computability.Circuit.Simulation

/-!
# Parallel circuits on disjoint inputs

`Circuit.parallel` runs two circuits on separate input blocks and concatenates their outputs.
Both total gate count and arbitrary weighted cost add exactly.

## Main definitions

* `Cslib.Circuits.Circuit.parallel`: run circuits on disjoint input blocks.

## Main results

* `Cslib.Circuits.Circuit.eval_parallel`: evaluation on the two input blocks.
* `Cslib.Circuits.Circuit.cost_program_parallel`: exact weighted cost.
-/

@[expose] public section

namespace Cslib.Circuits.Circuit

variable {σ : Signature} {U : Type*} {n m p q : ℕ}

/-- Run two circuits on disjoint input blocks, retaining sharing within each circuit. -/
def parallel (c : Circuit σ n m) (d : Circuit σ p q) : Circuit σ (n + p) (m + q) :=
  (c.comp (wiring σ (Fin.castAdd p))).append (d.comp (wiring σ (Fin.natAdd n)))

/-- `c.parallel d` evaluates `c` on the first `n` inputs and `d` on the last `p` inputs,
concatenating their outputs. -/
@[simp] theorem eval_parallel (c : Circuit σ n m) (d : Circuit σ p q)
    (I : Interpretation σ U) (x : Fin (n + p) → U) :
    (c.parallel d).eval I x =
      Fin.append (c.eval I (x ∘ Fin.castAdd p)) (d.eval I (x ∘ Fin.natAdd n)) := by
  simp only [parallel, eval_append, eval_comp, eval_wiring]

/-- Disjoint-input composition adds arbitrary weighted gate cost. -/
theorem cost_program_parallel (c : Circuit σ n m) (d : Circuit σ p q) (cost : σ.Op → ℕ) :
    (c.parallel d).program.cost cost = c.program.cost cost + d.program.cost cost := by
  simp only [parallel, cost_program_append, cost_program_comp, cost_program_wiring, Nat.zero_add]

/-- The size of `c.parallel d` is the sum of the sizes of `c` and `d`. -/
@[simp] theorem size_parallel (c : Circuit σ n m) (d : Circuit σ p q) :
    (c.parallel d).size = c.size + d.size := by
  simp only [parallel, size_append, size_comp, size_wiring, Nat.zero_add]

end Cslib.Circuits.Circuit
