/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.IncidenceEntryCorrectness
public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.IncidenceEntryBounds

/-! # Executable incidence-entry coefficients and structural selection clients -/

public section

namespace CslibFrontierTests.TensorNetworkIncidenceEntryCorrectness

open Cslib Cslib.Circuits.Frontier Cslib.Circuits.Frontier.IncidenceNetwork Cslib.BitString

/-- Two tests whose selected row has a nonzero negative coefficient of V. -/
abbrev tests : List (List (List ℕ)) := [[[0], [1]], [[2], [2, 3]]]

example : factorCoeffs 4 2 2 = [15, 6] := by decide
example : factorCoeffs 0 2 2 = [0, 0] := by decide
example : factorCoeffs 4 0 2 = [] := by decide
example : chosenBy [(0, 0), (0, 1)] [false, true] = [(0, 1)] := by decide
example : selected (rowBlocks 1 tests [3] 0) [3] = [(0, 0), (0, 1), (1, 2)] := by decide
example : incEntry (rowVertex 4 2 1 tests [3] 0).2 [true, true] = [0, 10] := by decide
example : incEntry (rowVertex 4 2 1 tests [2] 0).2 [true, true, true] = [] := by decide
example : colEntry (3, [0, 1, 2], [([(0, 0), (0, 1)], 1)]) [true] = [4] := by decide

example : subsetMobius (fun S : Finset ℕ => (S.card : ℤ) ^ 2) {0, 1} = 2 := by decide

/-- Repeated variables/rows and out-of-range indices do not require a supplied selection proof. -/
example (idx : List ℕ) :
    (selected (rowBlocks 2 [[[0], [0]], [[0], [0]]] [999] 0) idx).Nodup :=
  nodup_selected_rowBlocks _ _ _ _ _

/-- The source squarefree coefficient of this actual row is -6V modulo 16. The value [0,10]
checks the sign, truncation and the exact selected incidence set, rather than just the API type. -/
example : truncRingHom 4 2 (subsetMobius (rowPolynomial 2 tests)
    {(0, 0), (0, 1), (1, 2)}) = GaloisRingArith.val 4 (truncFl 2) [0, 10] := by
  have h := val_rowVertex 4 2 1 tests [3] 0 [true, true]
  have hv : validIndices (rowBlocks 1 tests [3] 0)
      (blockIndices (rowBlocks 1 tests [3] 0) [true, true]) = true := by decide
  have hs : selected (rowBlocks 1 tests [3] 0)
      (blockIndices (rowBlocks 1 tests [3] 0) [true, true]) =
        [(0, 0), (0, 1), (1, 2)] := by decide
  have he : incEntry (rowVertex 4 2 1 tests [3] 0).2 [true, true] = [0, 10] := by decide
  have ht : ((List.residueClass 1 tests.length 0).map (tests.getD · [])) = tests := by decide
  rw [hv, ite_eq_left rfl, hs, he, ht] at h
  simpa using h.symm

end CslibFrontierTests.TensorNetworkIncidenceEntryCorrectness
