/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.PolyTime.Int.DotProduct
import CslibFrontier.Foundations.Data.ZMod.DotProduct
import CslibFrontier.Crypto.Protocols.SigmaProtocol.Lyubashevsky.Signature.Efficient

/-! Canonical upstream arithmetic and its migrated protocol clients. -/

namespace ComplexityTests.ListDotProduct

open Cslib Turing.MultiTapeTM Mathlib.Tactic.Matrix
open Cslib.Crypto.Protocols.SigmaProtocol

/-- One native certificate charges the cutoff and both full signed-binary lists. -/
example : ComputableInPolyTime (fun p : ℕ × List ℤ × List ℤ =>
    ListMatrix.dotProduct p.1 p.2.1 p.2.2)
    (encPair encUnary (encPair (encList encIntBin) (encList encIntBin))) encIntBin :=
  ComputableInPolyTime.listDotProduct

example : ListMatrix.dotProduct 0 ([7] : List ℤ) [9] = 0 := by
  exact ListMatrix.dotProduct_zero _ _

/-- Missing entries are zero; excess entries do not contribute. -/
example : ListMatrix.dotProduct 3 ([2, -3] : List ℤ) [4] = 8 := by
  rw [ListMatrix.dotProduct_eq_sum_map_range]
  decide

example : ListMatrix.dotProduct 1 ([2, -3] : List ℤ) [4, 100] = 8 := by
  rw [ListMatrix.dotProduct_eq_sum_map_range]
  decide

example : ListMatrix.dotProduct 1 ([2 ^ 64] : List ℤ) [-(2 ^ 64)] = -(2 ^ 128) := by
  rw [ListMatrix.dotProduct_eq_sum_map_range]
  norm_num

/-- The pure bridge works over arbitrary rings without importing crypto definitions. -/
example (R : Type*) [Ring R] (a b : Fin 2 → R) :
    ListMatrix.dotProduct 2 (List.ofFn a) (List.ofFn b) = a 0 * b 0 + a 1 * b 1 := by
  rw [ListMatrix.dotProduct_ofFn, Fin.sum_univ_two]

/-- Both outcomes of the existing modular equation checker survive the migration. -/
example : lyubashevskyVerifyEqList 1 2 1 7 [[2, 3]] [[1]] [0] [2, 1] [false] = true := by
  simp only [lyubashevskyVerifyEqList, ListMatrix.dotProduct_eq_sum_map_range]
  decide

example : lyubashevskyVerifyEqList 1 2 1 7 [[2, 3]] [[1]] [0] [2, 2] [false] = false := by
  simp only [lyubashevskyVerifyEqList, ListMatrix.dotProduct_eq_sum_map_range]
  decide

/-- The actual native signer still emits the same commitment bytes. -/
example : lyubashevskySignCommitment
    ((((1, 2, 1, 6), (7, 2, 1)), [], [[2, 3]], []), [2, 1]) =
      encList encIntBin [0] := by
  simp only [lyubashevskySignCommitment, ListMatrix.dotProduct_eq_sum_map_range]
  decide

end ComplexityTests.ListDotProduct
