/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Circuit/Composition.lean`)

public import CslibFrontier.Computability.Circuit.Pi
public import CslibFrontier.Foundations.Data.BitString.Block
import Mathlib.Algebra.BigOperators.Fin

/-!
# Copies of a circuit on blocks of the input

`Circuit.blockwise C k` reads its `k * n` inputs as `k` blocks of `n` (`Cslib.BitString.block`)
and runs a copy of the single-output circuit `C` on each block. Output `i` is the output of `C` on
block `i` (`Circuit.eval_blockwise`). The size is `k` times the size of `C`
(`Circuit.size_blockwise`), and the depth is at most that of `C` (`Circuit.depth_blockwise_le`).
This is the circuit of a `k`-fold direct product `x ↦ (f x₁, …, f x_k)`.

## Main definitions

* `Cslib.Circuits.Circuit.blockwise`: `k` copies of a circuit on the blocks of the input.

## Main results

* `Cslib.Circuits.Circuit.eval_blockwise`, `Cslib.Circuits.Circuit.size_blockwise`,
  `Cslib.Circuits.Circuit.depth_blockwise_le`: the function, the size and an upper bound on the
  depth of the copies.
* `Cslib.Circuits.Circuit.Computes.blockwise`: the copies of a circuit computing `f` compute `f` on
  every block.
-/

@[expose] public section

namespace Cslib.Circuits.Circuit

variable {σ : Signature} {n : ℕ} {U : Type*}

/-- The single-output circuit `C` run on each of `k` blocks of `n` inputs, with output `i` the
output of `C` on block `i` (`Cslib.BitString.block`). -/
def blockwise (C : Circuit σ n 1) (k : ℕ) : Circuit σ (k * n) k :=
  pi fun i => C.comp (Circuit.wiring σ fun j => finProdFinEquiv (i, j))

/-- Output `i` of `blockwise C k` is the output of `C` on block `i` of the input. -/
@[simp] theorem eval_blockwise {I : Interpretation σ U} (C : Circuit σ n 1) (k : ℕ)
    (x : Fin (k * n) → U) :
    (blockwise C k).eval I x = fun i => C.eval I (BitString.block x i) 0 := by
  rw [blockwise, eval_pi]
  funext i
  rw [eval_comp, eval_wiring]
  rfl

/-- `blockwise C k` has `k` times as many gates as `C`. -/
@[simp] theorem size_blockwise (C : Circuit σ n 1) (k : ℕ) :
    (blockwise C k).size = k * C.size := by
  simp [blockwise]

/-- `blockwise C k` is at most as deep as `C`. -/
theorem depth_blockwise_le (C : Circuit σ n 1) (k : ℕ) : (blockwise C k).depth ≤ C.depth :=
  depth_pi_le _ fun _ => (depth_comp_le _ _).trans (by rw [depth_wiring, add_zero])

/-- If `C` computes `f`, then `blockwise C k` computes `f` on every block. -/
theorem Computes.blockwise {I : Interpretation σ U} {C : Circuit σ n 1} {f : (Fin n → U) → U}
    (hC : C.Computes I (single f)) (k : ℕ) :
    (C.blockwise k).Computes I fun x i => f (BitString.block x i) := fun x => by
  rw [eval_blockwise]
  exact funext fun i => hC _ ▸ rfl

end Cslib.Circuits.Circuit
