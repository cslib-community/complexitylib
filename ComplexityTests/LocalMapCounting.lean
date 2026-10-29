/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module

public import Complexity.Init
public import Complexity.Computability.Complexity.FineGrained.LocalMapCounting

/-!
# Kernel-checked tests for `Cslib.Complexity.FineGrained.LocalMapCounting`

Concrete `decide` checks for constant-locality Boolean maps, their CSP and exact-multiplicity CNF
reductions, preimage counting, and self-reduction preimage finding (Corollary C.2).
-/

@[expose] public section

namespace ComplexityTests.LocalMapCounting

open Cslib.Complexity Cslib.Logic.PL

/-- Local output computing `x₀ ^^ x₁` on scope `[0, 1]` (accepting `[0, 1]` and `[1, 0]`). -/
def xor01 : LocalOutput :=
  ([0, 1], [[false, true], [true, false]])

/-- Local output computing `x₁ && x₂` on scope `[1, 2]` (accepting pattern `[1, 1]`). -/
def and12 : LocalOutput :=
  ([1, 2], [[true, true]])

/-- A 2-local map `G : {0, 1}³ → {0, 1}²` given by `G(x₀, x₁, x₂) = (x₀ ^^ x₁, x₁ && x₂)`. -/
def map3to2 : LocalMap :=
  (3, [xor01, and12])

/-! ### 1. Validity and Evaluation on Concrete Maps -/

example :
    map3to2.Valid 2 = true ∧
    map3to2.Valid 1 = false ∧
    map3to2.numVars = 3 ∧
    map3to2.numOutputs = 2 ∧
    map3to2.evalBits [false, false, false] = [false, false] ∧
    map3to2.evalBits [true, false, true] = [true, false] ∧
    map3to2.evalBits [true, true, true] = [false, true] := by
  decide

/-! ### 2. CSP / Exact-Multiplicity CNF Reduction and Preimage Counts -/

-- A 1-local map `G : {0, 1}² → {0, 1}²` with constant-zero outputs (`satTable = []`).
def zeroMap : LocalMap :=
  (2, [([0], []), ([0], [])])

-- Preimage counts and CSP / declared-CNF reductions on `[false, false]` (3 preimages),
-- `[false, true]` (1 preimage), mismatched target `[true]` (0 preimages), and `zeroMap`.
example :
    map3to2.preimageCount [false, false] = 3 ∧
    (map3to2.toCSP [false, false]).modelCountOn LocalMap.cspSem (Finset.range 3) = 3 ∧
    (LocalMap.toDeclaredCNF 2 (map3to2, [false, false])).2.modelCountOn (Finset.range 3) = 3 ∧
    map3to2.preimageCount [false, true] = 1 ∧
    (map3to2.toCSP [false, true]).modelCountOn LocalMap.cspSem (Finset.range 3) = 1 ∧
    (LocalMap.toDeclaredCNF 2 (map3to2, [false, true])).2.modelCountOn (Finset.range 3) = 1 ∧
    map3to2.preimageCount [true] = 0 ∧
    (LocalMap.toDeclaredCNF 2 (map3to2, [true])).2.modelCountOn (Finset.range 3) = 0 ∧
    zeroMap.Valid 1 = true ∧
    zeroMap.preimageCount [true, true] = 0 ∧
    zeroMap.preimageCount [false, false] = 4 := by
  decide

/-! ### 3. Prefix Self-Reduction and Preimage Finding -/

example :
    map3to2.findPreimage 2 [false, true] = some [true, true, true] ∧
    map3to2.findPreimage 2 [false, false] = some [false, false, false] ∧
    zeroMap.findPreimage 1 [true, true] = none ∧
    zeroMap.findPreimage 1 [false, false] = some [false, false] ∧
    map3to2.findPreimage 1 [false, true] = none := by
  decide

end ComplexityTests.LocalMapCounting
