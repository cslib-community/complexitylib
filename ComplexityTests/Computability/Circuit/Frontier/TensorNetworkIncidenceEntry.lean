/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.IncidenceEntryCertificate

/-!
# Tests for the entries of the incidence network of Lemma D.2

A block of the two incidences `(0, 0), (0, 1)` with one selected has one index wire: the index
`0` selects `(0, 1)` and the index `1` selects `(0, 0)`, in the lexicographic order of the
combinations. At the index `1`, a column of the variables `0, 1, 2` with that block has two
unselected variables, so its entry is `2 ^ 2` modulo `2 ^ 3`. A block of three incidences of test
`1` with two selected has `⌈log₂ 3⌉ = 2` wires; the index `3` is invalid, so the row has entry
zero.
-/

@[expose] public section

namespace ComplexityTests.TensorNetworkIncidenceEntry

open Cslib.Circuits.Frontier Cslib.Circuits.Frontier.IncidenceNetwork

/-- A block of two incidences of test `0`, one selected. -/
abbrev b₁ : Block := ([(0, 0), (0, 1)], 1)

/-- A block of three incidences of test `1`, two selected. -/
abbrev b₂ : Block := ([(1, 0), (1, 1), (1, 2)], 2)

example : blockWires b₁ = 1 := by decide
example : blockWires b₂ = 2 := by decide
example : blockIndices [b₁, b₂] [true, false, true] = [1, 2] := by decide
example : selectBlock b₁ 0 = [(0, 1)] := by decide
example : selectBlock b₁ 1 = [(0, 0)] := by decide
example : selected [b₁, b₂] [1, 2] = [(0, 0), (1, 0), (1, 1)] := by decide
example : validIndices [b₁, b₂] [1, 2] = true := by decide
example : validIndices [b₁, b₂] [1, 3] = false := by decide

-- The column of the variables `0, 1, 2`: the index `1` selects variable `0`.
example : colEntry (3, [0, 1, 2], [b₁]) [true] = [4] := by decide

-- An invalid index gives the row entry zero.
example : rowEntry (2, 1, [[[0]]], [b₂]) [true, true] = [] :=
  rowEntry_of_not_valid (by decide)

-- The certificate bound is not vacuous: its constant exists.
example : ∃ c : ℕ, ∀ q : Desc × List Bool,
    incCertificate.time q ≤ c * ((Turing.MultiTapeTM.encPair encDesc
      Turing.MultiTapeTM.encBits q).length + 1) ^ c * 2 ^ descInc q.1 :=
  let ⟨c, h⟩ := exists_incCertificate_le
  ⟨c, fun q => (h q).1⟩

end ComplexityTests.TensorNetworkIncidenceEntry
