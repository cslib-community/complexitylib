/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.LogSpace.Randomized.CompactTimeLayer
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.FairCoin.ClockedTable

/-!
# Exact interpretation of the initialized clocked coin table

The two threshold bits emitted by `clockedCoinTableProgram` recover every entry of the existing
`Matrix.finTimeLayer` of the actual compact coin matrix. This includes invalid configurations,
off-clock entries and terminal rows; no represented-view or reachability premise is needed.
The finite terminal reward also agrees with the local `clockedAccept` computation.

Together with `computableInLogSpace_clockedCoinTable`, this gives native initialized serialization
of the matrix payload in the canonical BPL construction. A complete serialized instance with
dimension, start and reward fields, directed paired ports, and the native estimator remain open.

## Main results

* `Turing.MultiTapePTM.ConfigurationGraph.finTimeLayer_compactCoinMatrix_eq_clockedCoinCount`:
  every clocked matrix entry is half the guarded base count.
* `Turing.MultiTapePTM.ConfigurationGraph.finTimeLayer_compactCoinMatrix_eq_clockedCoinTable`:
  the initialized native output gives every clocked matrix entry exactly.
* `Turing.MultiTapePTM.ConfigurationGraph.finTimeLayerReward_eq_clockedAccept`:
  the terminal reward equals its local native predicate.
-/

public section

namespace Turing.MultiTapePTM.ConfigurationGraph

open MultiTapeNTM.ConfigurationGraph Matrix

variable {k : ℕ} {State : Type} [Fintype State] {machine : MultiTapePTM k Bool State}
  {R : Type*} [Field R]

/-- Every numeric clocked entry is half the guarded base count, including invalid IDs and
terminal rows. The input symbol is read at the base source's input position. -/
theorem finTimeLayer_compactCoinMatrix_eq_clockedCoinCount (B T : ℕ) (w : List Bool)
    (u v : Fin ((T + 1) * vertexBound (k := k) B)) :
    finTimeLayer T (compactCoinMatrix machine R B w) u v =
      (clockedCoinCountWithSymbol machine B w.length u v
        w[queryIndex (k := k) B (u.val % vertexBound (k := k) B)]? : R) / 2 := by
  rw [finTimeLayer_apply]
  dsimp only [clockedCoinCountWithSymbol, compactCoinMatrix]
  split_ifs <;> simp

/-- The two output bits at the row-major address give the exact finite time-layer matrix entry.
This interprets the initialized writer's payload on the same consecutive IDs as the BPL theorem. -/
theorem finTimeLayer_compactCoinMatrix_eq_clockedCoinTable (D d : ℕ) (w : List Bool)
    (u v : Fin (clockedVertexBound (k := k) D d w.length)) :
    finTimeLayer (2 * (2 * (w.length + 1)) ^ d)
        (compactCoinMatrix machine R (radix D w.length) w) u v =
      (((clockedCoinTable machine D d w).getD
          (2 * (u.val * clockedVertexBound (k := k) D d w.length + v.val)) false).toNat +
        ((clockedCoinTable machine D d w).getD
          (2 * (u.val * clockedVertexBound (k := k) D d w.length + v.val) + 1)
          false).toNat : ℕ) / 2 := by
  rw [clockedCoinTable_count]
  exact finTimeLayer_compactCoinMatrix_eq_clockedCoinCount _ _ _ _ _

/-- The terminal reward on consecutive IDs is the local native accepting-ID predicate.
This equality concerns the value, without packaging it into the matrix payload. -/
theorem finTimeLayerReward_eq_clockedAccept (B n T : ℕ)
    (u : Fin ((T + 1) * vertexBound (k := k) B)) :
    finTimeLayerReward T (compactAcceptVec (k := k) (State := State) R B n) u =
      ((clockedAccept (k := k) (State := State) B n T u).toNat : R) := by
  change (if u.val / vertexBound (k := k) B = T then
    (if bad (k := k) (State := State) B n (u.val % vertexBound (k := k) B) then 1 else 0)
    else 0) = _
  dsimp only [clockedAccept]
  split_ifs <;> simp_all

end Turing.MultiTapePTM.ConfigurationGraph
