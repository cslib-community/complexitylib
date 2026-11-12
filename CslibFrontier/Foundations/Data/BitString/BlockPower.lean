/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.Block
public import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators

/-!
# Cartesian powers of sets of blocks

The `m`-th Cartesian power of a finite set `S` of tuples of `k` entries, as a set of tuples of
`m * k` entries (`Cslib.BitString.blockPower`): the tuples whose `m` blocks of `k` entries
(`Cslib.BitString.block`) all lie in `S`. It has `#S ^ m` elements
(`Cslib.BitString.card_blockPower`), as cutting a tuple into its blocks is an equivalence
(`Cslib.BitString.blocksEquiv`). Raising a set to a power before hashing it turns an
approximation of its size within a constant factor into one within a factor that tends to `1`,
the amplification used in approximate counting.

## Main definitions

* `Cslib.BitString.blockPower`: the tuples all of whose blocks lie in a set.

## Main results

* `Cslib.BitString.mem_blockPower`: membership is membership of every block.
* `Cslib.BitString.card_blockPower`: the size of the power.
-/

public section

namespace Cslib.BitString

open Finset

variable {α : Type*} {m k : ℕ}

/-- The `m`-th Cartesian power of a set `S` of tuples of `k` entries: the tuples of `m * k`
entries whose `m` blocks all lie in `S`. -/
def blockPower (S : Finset (Fin k → α)) (m : ℕ) : Finset (Fin (m * k) → α) :=
  (Fintype.piFinset fun _ : Fin m => S).map blocksEquiv.symm.toEmbedding

/-- A tuple lies in the `m`-th power of `S` exactly when each of its blocks lies in `S`. -/
@[simp] theorem mem_blockPower {S : Finset (Fin k → α)} {x : Fin (m * k) → α} :
    x ∈ blockPower S m ↔ ∀ i, block x i ∈ S := by
  rw [blockPower, mem_map_equiv, Equiv.symm_symm, Fintype.mem_piFinset, blocksEquiv_apply]

/-- The `m`-th power of `S` has `#S ^ m` elements. -/
@[simp] theorem card_blockPower (S : Finset (Fin k → α)) (m : ℕ) :
    #(blockPower S m) = #S ^ m := by
  rw [blockPower, card_map, Fintype.card_piFinset_const]

/-- The power of the empty set with at least one block is empty. -/
theorem blockPower_eq_empty_iff {S : Finset (Fin k → α)} (hm : m ≠ 0) :
    blockPower S m = ∅ ↔ S = ∅ := by
  rw [← card_eq_zero, card_blockPower, Nat.pow_eq_zero, card_eq_zero, and_iff_left hm]

end Cslib.BitString
