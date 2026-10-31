/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Quantum.PathNetwork

/-! The tensor network of a circuit and its mirror copy: concrete contractions that equal the
acceptance gaps and other projected gaps of small circuits, computed directly and through
`contraction_network`. -/

namespace ComplexityTests.QuantumPathNetwork

open Cslib Cslib.Quantum Cslib.Quantum.PathNetwork Cslib.Circuits.Frontier

/-! ### Direct contractions -/

-- One Hadamard gate on `|0⟩`: one of the four pairs of paths accepts, so the gap is `1`. The
-- network has one occurrence, so four edges: sixteen assignments.
example : (network (-1 : ℤ) [0] [false] [(true, 0, [])]).2.contraction = 1 := by decide
example : acceptGap [(true, 0, [])] [false] = 1 := by decide

-- A NOT gate on `|0⟩` accepts with certainty and has no Hadamard gate.
example : (network (-1 : ℤ) [0] [false] [(false, 0, [])]).2.contraction = 1 := by decide

-- A NOT gate on `|1⟩` rejects with certainty.
example : (network (-1 : ℤ) [0] [true] [(false, 0, [])]).2.contraction = 0 := by decide

-- Without gates the network is the scalar vertex alone: it reads the input bit of qubit `0`.
example : (network (-1 : ℤ) [0] [true] []).2.contraction = 1 := by decide
example : (network (-1 : ℤ) [0] [false] []).2.contraction = 0 := by decide

-- An untouched qubit `0` set to one: the gate on qubit `1` does not matter, the gap is `2 ^ 1`.
example : (network (-1 : ℤ) [0] [true, false] [(true, 1, [])]).2.contraction = 2 := by decide

/-! ### Through the identity -/

-- Two Hadamard gates interfere; the signed entries `-1` cancel the four accepting pairs from
-- `|0⟩` and add them up from `|1⟩`.
example : (network (-1 : ℤ) [0] [false] [(true, 0, []), (true, 0, [])]).2.contraction = 0 := by
  rw [contraction_network _ _ _ (by decide)]
  decide
example : (network (-1 : ℤ) [0] [true] [(true, 0, []), (true, 0, [])]).2.contraction = 4 := by
  rw [contraction_network _ _ _ (by decide)]
  decide

-- A Hadamard gate copied by a CNOT into qubit `0`: probability `1 / 2`, gap `1`.
example :
    (network (-1 : ℤ) [0] [false, false] [(true, 1, []), (false, 0, [1])]).2.contraction = 1 := by
  rw [contraction_network _ _ _ (by decide)]
  decide

/-! ### Other measured qubits -/

-- Measuring no qubit gives the squared norm `2 ^ h`.
example : (network (-1 : ℤ) [] [false] [(true, 0, [])]).2.contraction = 2 := by decide

-- An untouched measured qubit is read from the input register by the scalar vertex.
example : (network (-1 : ℤ) [1] [false, true] [(true, 0, [])]).2.contraction = 2 := by decide
example : (network (-1 : ℤ) [1] [false, false] [(true, 0, [])]).2.contraction = 0 := by decide

-- The Hadamard gate copied into qubit `0` leaves qubits `0` and `1` equal: both read `1` with
-- probability `1 / 2`, the same as qubit `1` alone.
example :
    (network (-1 : ℤ) [0, 1] [false, false] [(true, 1, []), (false, 0, [1])]).2.contraction =
      1 := by
  rw [contraction_network _ _ _ (by decide)]
  decide
example :
    (network (-1 : ℤ) [1] [false, false] [(true, 1, []), (false, 0, [1])]).2.contraction = 1 := by
  rw [contraction_network _ _ _ (by decide)]
  decide

/-! ### Residues over `ℕ` -/

-- Over `ℕ` the Hadamard sign is `2 ^ P - 1`; modulo `2 ^ P` the contraction is the gap.
example :
    (network (2 ^ 3 - 1 : ℕ) [0] [true] [(true, 0, []), (true, 0, [])]).2.contraction % 2 ^ 3 =
      4 := by
  rw [contraction_network_mod _ _ _ (by decide) (by decide)]
  decide

/-! ### Sizes -/

-- Four edges per occurrence: the Toffoli gate has three occurrences.
example : (network (-1 : ℤ) [0] [false, false, false] [(false, 2, [0, 1])]).2.numEdges = 12 := by
  decide

end ComplexityTests.QuantumPathNetwork
