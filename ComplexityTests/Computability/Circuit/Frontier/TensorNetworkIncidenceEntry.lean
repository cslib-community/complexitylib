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

**A valid row.** The tests `x₀ + x₁` and `x₂ + x₂ x₃` form one group (`J = 1`). At precision
`P = 4`, truncation order `ℓ = 2` and three selected incidences, their row is the row vertex of the
incidence network, with the four incidences `(0, 0), (0, 1), (1, 2), (1, 3)` in one block and two
index wires. For `ℓ = 2` the parity factor is `B(y; V) = (1 - y) + (2 y - 1) y (y - 1) V`, since
`parityLinearCoeffs 2 = [(1, -1), (-1, 2)]`: `B(0) = 1`, `B(1) = 0` and `B(2) = -1 + 6 V`. The
entry is `∏_t ∑_{T ⊆ S_t} (-1) ^ (|S_t| - |T|) B(m_t(T))`, for `m_t(T)` the monomials of test `t`
inside `T`.
* The index `3` selects `S₀ = {x₀, x₁}` and `S₁ = {x₂}`. Test `0` has `m₀(T) = 0, 1, 1, 2` on
  `T = ∅, {x₀}, {x₁}, {x₀, x₁}`, and test `1` has `m₁(T) = 0, 1` on `T = ∅, {x₂}`. So the entry is
  `(B(0) - 2 B(1) + B(2)) (B(1) - B(0)) = 6 V · (-1) = -6 V`, that is `10 V` modulo `16`.
* The index `0` selects `S₀ = {x₁}` and `S₁ = {x₂, x₃}`, with `m₁(T) = 0, 1, 0, 2` on
  `T = ∅, {x₂}, {x₃}, {x₂, x₃}`. The entry is `(B(1) - B(0)) (B(0) - B(1) - B(0) + B(2))`,
  which is `(-1) (-1 + 6 V) = 1 - 6 V`, that is `1 + 10 V`.
* The index `2` selects `S₁ = {x₃}`, inside which test `1` has no monomial, so the entry is `0`.

The tests check these coefficients, and the product of the per-test subset sums in `B_{4,2}`. The
signs matter: summing the subsets without signs would give `6 V` and `1 + 6 V`.
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

/-! ### A valid row -/

/-- The tests `x₀ + x₁` and `x₂ + x₂ x₃`. -/
abbrev sys : List (List (List ℕ)) := [[[0], [1]], [[2], [2, 3]]]

/-- The block of their incidences, three selected. -/
abbrev blk : Block := ([(0, 0), (0, 1), (1, 2), (1, 3)], 3)

/-- Their row at precision `4` and truncation order `2`. -/
abbrev row : RowDesc := (4, 2, sys, [blk])

-- It is the row vertex of the incidence network with one group, on the index wires `0, 1`.
example : rowVertex 4 2 1 sys [3] 0 = ([0, 1], .inl row) := rfl

-- The bits read the indices little-endian, and every index is valid.
example : blockIndices [blk] [true, true] = [3] := by decide
example : blockIndices [blk] [false, true] = [2] := by decide
example : validIndices [blk] [3] = true := by decide
example : selected [blk] [3] = [(0, 0), (0, 1), (1, 2)] := by decide
example : selected [blk] [0] = [(0, 1), (1, 2), (1, 3)] := by decide
example : selected [blk] [2] = [(0, 0), (0, 1), (1, 3)] := by decide

-- The parity factor `B(y; V) = (1 - y) + (2 y - 1) y (y - 1) V` modulo `2 ^ 4`.
example : Cslib.parityLinearCoeffs 2 = [(1, -1), (-1, 2)] := by decide
example : factorCoeffs 4 2 0 = [1, 0] := by decide
example : factorCoeffs 4 2 1 = [0, 0] := by decide
example : factorCoeffs 4 2 2 = [15, 6] := by decide

-- The index `3`: `-6 V`.
example : rowEntry row [true, true] = [0, 10] := by decide

-- The index `3` is the product of the per-test subset sums `B(0) - 2 B(1) + B(2)` and
-- `B(1) - B(0)` in `B_{4,2}`.
open Cslib.GaloisRingArith in
example : rowEntry row [true, true] =
    mul 4 (truncFl 2)
      (add 4 (truncFl 2)
        (sub 4 (truncFl 2) (sub 4 (truncFl 2) (factorCoeffs 4 2 0) (factorCoeffs 4 2 1))
          (factorCoeffs 4 2 1))
        (factorCoeffs 4 2 2))
      (sub 4 (truncFl 2) (factorCoeffs 4 2 1) (factorCoeffs 4 2 0)) := by decide

-- The index `0`: `1 - 6 V`.
example : rowEntry row [false, false] = [1, 10] := by decide

-- The index `2`: test `1` has no monomial inside `{x₃}`.
example : rowEntry row [false, true] = [0, 0] := by decide

-- The certificate bound is not vacuous: its constant exists.
example : ∃ c : ℕ, ∀ q : Desc × List Bool,
    incCertificate.time q ≤ c * ((Turing.MultiTapeTM.encPair encDesc
      Turing.MultiTapeTM.encBits q).length + 1) ^ c * 2 ^ descInc q.1 :=
  let ⟨c, h⟩ := exists_incCertificate_le
  ⟨c, fun q => (h q).1⟩

end ComplexityTests.TensorNetworkIncidenceEntry
