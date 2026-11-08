/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (test driver)

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.IncidenceWireRanks
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.IncidencePadding
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.IncidenceGroupCoefficients
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.IncidenceColumnWeights

/-! # Shared physical wires, assignment coverage, forced padding and actual group products -/

public section

namespace ComplexityTests.TensorNetworkIncidenceGlobal

open Cslib Cslib.BitString Cslib.Circuits.Frontier Cslib.Circuits.Frontier.IncidenceNetwork
open Polynomial GaloisRingArith

/-- Four positive-width blocks: row order and column order are different. -/
abbrev sys : List (List (List ℕ)) := [[[0], [1]], [[0], [1]], [[0], [1]], [[0], [1]]]

example : numWires 2 sys [1, 1, 1, 1] = 4 := by decide
example : rowPorts 2 sys [1, 1, 1, 1] 0 = [0, 1] ∧
    colPorts 2 sys [1, 1, 1, 1] 0 = [0, 2] := by decide
example : blockIndices (rowBlocks 2 sys [1, 1, 1, 1] 0)
      (DescribedNetwork.wordBits [true, false, true, true]
        (rowPorts 2 sys [1, 1, 1, 1] 0)) = [1, 0] ∧
    blockIndices (colBlocks 2 sys [1, 1, 1, 1] 0)
      (DescribedNetwork.wordBits [true, false, true, true] (colPorts 2 sys [1, 1, 1, 1] 0)) =
        [1, 1] := by decide
example : blockIndices (rowBlocks 2 sys [0, 0, 0, 0] 0) [] = [0, 0] ∧
    blockIndices (colBlocks 2 sys [0, 0, 0, 0] 0) [] = [0, 0] := by decide

example (word : List Bool) :
    (blockIndices (rowBlocks 2 sys [1, 1, 1, 1] 1)
      (DescribedNetwork.wordBits word (rowPorts 2 sys [1, 1, 1, 1] 1))).getD 0 0 =
    (blockIndices (colBlocks 2 sys [1, 1, 1, 1] 0)
      (DescribedNetwork.wordBits word (colPorts 2 sys [1, 1, 1, 1] 0))).getD 1 0 :=
  row_col_index_eq _ _ _ _ _ _ (by decide) (by decide)

/-- All ranks here are genuinely fitting combination ranks, not arbitrary binary indices. -/
example : ∃! x : Fin (numWires 2 sys [1, 1, 1, 1]) → Bool,
    ∀ b : Fin (2 * 2), wireIndex 2 sys [1, 1, 1, 1] (List.ofFn x) (b / 2) (b % 2) = b % 2 := by
  exact existsUnique_wireAssignment 2 sys [1, 1, 1, 1] (fun b => b % 2) (by decide)

/-- Zero-width blocks and the empty main-wire space have exactly one assignment. -/
example : ∃! x : Fin (numWires 1 [] [0]) → Bool,
    ∀ b : Fin (1 * 1), wireIndex 1 [] [0] (List.ofFn x) (b / 1) (b % 1) = 0 := by
  exact existsUnique_wireAssignment 1 [] [0] (fun _ => 0) (by decide)
example : ∃! x : Fin (numWires 0 [] []) → Bool,
    ∀ b : Fin (0 * 0), wireIndex 0 [] [] (List.ofFn x) (b / 0) (b % 0) = 0 := by
  exact existsUnique_wireAssignment 0 [] [] (fun _ => 0) (by intro b; exact b.elim0)

example : (∑ x : Fin (2 + 3) → Bool,
    if ∀ i : Fin 3, x (Fin.natAdd 2 i) = false then (1 : ℕ) else 0) = 4 := by
  rw [sum_padding_false 2 3 (fun _ => (1 : ℕ))]
  decide

/-- Arbitrarily many padding edges preserve this live network's actual coefficient readback. -/
example : Cslib.Complexity.CountingSimulation.truncCoeffSum incEntry
      (4, 2, network 4 2 2 4 9 2 sys [1, 1, 1, 1]) =
    Cslib.Complexity.CountingSimulation.truncCoeffSum incEntry
      (4, 2, network 4 2 2 4 0 2 sys [1, 1, 1, 1]) :=
  truncCoeffSum_network_padding _ _ _ _ _ _ _ _
example : (network 4 2 2 0 9 2 sys [1, 1, 1, 1]).2.polyContraction incEntry =
    (network 4 2 2 0 0 2 sys [1, 1, 1, 1]).2.polyContraction incEntry :=
  polyContraction_network_padding _ _ _ _ _ _ _ _

/-- Variables 2 and 3 occur in no test, but both remain free in the actual global weight. -/
example : unselectedCount (List.range 4)
    (allRowSelected 2 sys [1, 1, 1, 1] [true, false, true, true]) = 2 := by decide
example : (∏ h ∈ Finset.range 2, val 4 (truncFl 2)
    (incEntry (colVertex 4 2 4 sys [1, 1, 1, 1] h).2
      (DescribedNetwork.wordBits [true, false, true, true]
        (colPorts 2 sys [1, 1, 1, 1] h)))) = (4 : Ring 4 (truncFl 2)) := by
  rw [val_colVertices_prod 4 2 2 4 (by decide) sys [1, 1, 1, 1] [true, false, true, true]]
  rw [show unselectedCount (List.range 4)
    (allRowSelected 2 sys [1, 1, 1, 1] [true, false, true, true]) = 2 from by decide]
  norm_num

example : subsetMobius
    (fun T : Finset (ℕ × ℕ) =>
      ∏ t ∈ ({0, 1} : Finset ℕ), ((T.filter fun p => p.1 = t).card + 1 : ℤ))
    {(0, 0), (1, 1)} = 1 := by decide

/-- A genuine constructed coefficient product retains its negative coefficient modulo 16. -/
abbrev tests : List (List (List ℕ)) := [[[0], [1]], [[2], [2, 3]]]

example : (∏ t ∈ Finset.range 2, truncRingHom 4 2
    (subsetMobius (fun T => parityFactor 2 (monomialsIn (tests.getD t []) t T.toList : ℤ))
      (([(0, 0), (0, 1), (1, 2)] : List (ℕ × ℕ)).toFinset.filter fun p => p.1 = t))) =
        val 4 (truncFl 2) [0, 10] := by
  have h := val_rowVertex_prod 4 2 1 tests [3] 0 [true, true]
  dsimp only at h
  have hv : validIndices (rowBlocks 1 tests [3] 0)
      (blockIndices (rowBlocks 1 tests [3] 0) [true, true]) = true := by decide
  have hs : selected (rowBlocks 1 tests [3] 0)
      (blockIndices (rowBlocks 1 tests [3] 0) [true, true]) =
        [(0, 0), (0, 1), (1, 2)] := by decide
  have he : incEntry (rowVertex 4 2 1 tests [3] 0).2 [true, true] = [0, 10] := by decide
  have ht : ((List.residueClass 1 tests.length 0).map (tests.getD · [])) = tests := by decide
  rw [hv, ite_eq_left rfl, hs, he, ht] at h
  exact h.symm

end ComplexityTests.TensorNetworkIncidenceGlobal
