/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests of Williams simulation and quantitative bounds)

public import Complexity.Computability.Complexity.Classes.TimeSpace.Williams
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Streaming

/-!
# Square-root-space theorem clients

The parity language exercises the final inclusion with a concrete linear-time source and both
accepting and rejecting words. A lifted instance type checks the arbitrary-universe encoding
bridge on a satisfiable constant-machine example. Capacity examples exercise exact binary
storage rather than the exponentially many assignments.
-/

public section

namespace ComplexityTests.Williams

open Cslib.Complexity
open _root_.Turing.MultiTapeTM
open _root_.Turing.MultiTapePTM.BlockComputation
open Cslib.TreeEval.Ary.Packed

/-- Parity of the number of true input bits. -/
def oddOnes (word : List Bool) : Bool := word.foldl (fun b x => b ^^ x) false

example : oddOnes [true, false, true, true] = true ∧ oddOnes [true, true] = false := by decide

private theorem oddOnes_mem_DTIME : {w | oddOnes w = true} ∈ DTIME encBits id :=
  setOf_mem_DTIME_of_computableInO
    (ComputableTidilyInO.foldl_bits_finite encBool (fun b x => b ^^ x) false).computableInO
    (fun _ => le_rfl)

example : {w | oddOnes w = true} ∈
    DSPACE encBits (fun n => Nat.sqrt (n * (Nat.log2 n + 1))) :=
  DTIME_subset_DSPACE_sqrt encBits id (fun _ => le_rfl) oddOnes_mem_DTIME

/-- This instance type deliberately lives above the machine-state universe. -/
private def liftedEncoding : ULift.{1} (List Bool) ↪ List Bool :=
  ⟨ULift.down, ULift.down_injective⟩

private theorem lifted_univ_mem_DTIME : (Set.univ : Set (ULift.{1} (List Bool))) ∈
    DTIME liftedEncoding id := by
  obtain ⟨c, h⟩ := computableInTimeAndSpace_of_const (encIn := liftedEncoding)
    (encOut := encBool) true
  exact ⟨0, c, fun _ => 0, decidableInTimeAndSpace_iff.mpr
    ⟨Function.const (ULift.{1} (List Bool)) true,
      by simpa only [Nat.zero_mul, Nat.zero_add] using h,
      fun _ => by simp⟩⟩

example : (Set.univ : Set (ULift.{1} (List Bool))) ∈
    DSPACE liftedEncoding (fun n => Nat.sqrt (n * (Nat.log2 n + 1))) :=
  DTIME_subset_DSPACE_sqrt liftedEncoding id (fun _ => le_rfl) lifted_univ_mem_DTIME

example : (((2 ^ chunkWidth 1 6) ^ (1 * chunkCount 1 6)) : ℕ).size = 7 := by decide
example : (((2 ^ chunkWidth 3 17) ^ (3 * chunkCount 3 17)) : ℕ).size = 55 := by decide
example : BalancedParameters.blockWidth 1024 + BalancedParameters.horizon 1024 *
    ((BalancedParameters.blockWidth 1024).size + 1) = 200 := by decide

end ComplexityTests.Williams
