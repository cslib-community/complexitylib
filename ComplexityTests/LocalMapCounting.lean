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

Concrete `decide` checks and end-to-end theorem instantiations for constant-locality Boolean maps,
their CSP and exact-multiplicity CNF reductions, preimage counting, decision, and self-reduction
preimage finding (Corollary C.2).
-/

@[expose] public section

namespace ComplexityTests.LocalMapCounting

open Cslib.Complexity Cslib.Complexity.CountingNativeEndpoint
open Cslib.Complexity.SubexponentialSAT Cslib.Logic.PL

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

example : map3to2.Valid 2 = true := by decide
example : map3to2.Valid 1 = false := by decide
example : map3to2.numVars = 3 ∧ map3to2.numOutputs = 2 := by decide

example : map3to2.evalBits [false, false, false] = [false, false] := by decide
example : map3to2.evalBits [true, false, true] = [true, false] := by decide
example : map3to2.evalBits [true, true, true] = [false, true] := by decide

/-! ### 2. CSP / Exact-Multiplicity CNF Reduction and Preimage Counts -/

-- For target `[false, false]`: `x₁ && x₂ = false` and `x₀ = x₁`.
-- Solutions in `{0, 1}³`: `(0, 0, 0)`, `(0, 0, 1)`, `(1, 1, 0)` -> 3 preimages.
example : map3to2.preimageCount [false, false] = 3 := by decide
example :
    (map3to2.toCSP [false, false]).modelCountOn LocalMap.cspSem (Finset.range 3) = 3 := by decide
example :
    (toDeclaredCNF 2 (map3to2, [false, false])).2.modelCountOn (Finset.range 3) = 3 := by decide

-- For target `[false, true]`: `x₁ && x₂ = true` (so `x₁ = x₂ = 1`) and `x₀ = x₁ = 1`.
-- Unique solution: `(1, 1, 1)` -> 1 preimage.
example : map3to2.preimageCount [false, true] = 1 := by decide
example :
    (map3to2.toCSP [false, true]).modelCountOn LocalMap.cspSem (Finset.range 3) = 1 := by decide
example :
    (toDeclaredCNF 2 (map3to2, [false, true])).2.modelCountOn (Finset.range 3) = 1 := by decide

-- Target of mismatched length has 0 preimages and reduces via `toDeclaredCNF` to `[[]]`.
example : map3to2.preimageCount [true] = 0 := by decide
example : (toDeclaredCNF 2 (map3to2, [true])).2.modelCountOn (Finset.range 3) = 0 := by decide

-- A 1-local map `G : {0, 1}² → {0, 1}²` with constant-zero outputs (`satTable = []`).
def zeroMap : LocalMap :=
  (2, [([0], []), ([0], [])])

example : zeroMap.Valid 1 = true := by decide
example : zeroMap.preimageCount [true, true] = 0 := by decide
example : zeroMap.preimageCount [false, false] = 4 := by decide

/-! ### 3. Prefix Self-Reduction and Preimage Finding -/

example : map3to2.findPreimage 2 [false, true] = some [true, true, true] := by decide
example : map3to2.findPreimage 2 [false, false] = some [false, false, false] := by decide
example : zeroMap.findPreimage 1 [true, true] = none := by decide
example : zeroMap.findPreimage 1 [false, false] = some [false, false] := by decide

-- Invalid locality returns `none`.
example : map3to2.findPreimage 1 [false, true] = none := by decide

/-! ### 4. End-to-End Theorem Instantiations -/

example (G : LocalMap) (target : List Bool) (hlen : target.length = G.numOutputs) :
    G.preimageCount target =
      (G.toCSP target).modelCountOn LocalMap.cspSem (Finset.range G.numVars) :=
  G.preimageCount_eq_modelCountOn_toCSP hlen

example (k : ℕ) (q : LocalMap × List Bool) :
    (toDeclaredCNF k q).2.modelCountOn (Finset.range (toDeclaredCNF k q).1) =
      if q.1.Valid k then q.1.preimageCount q.2 else 0 :=
  modelCountOn_toDeclaredCNF k q

example (k : ℕ) :
    ∃ (count : LocalMap × List Bool → ℕ) (A e b : ℕ),
      (∀ q : LocalMap × List Bool, q.1.Valid k = true → count q = q.1.preimageCount q.2) ∧
      Turing.MultiTapeTM.ComputableInO count encLocalMapQuery Turing.MultiTapeTM.encNat
        (fun q => ⌈(2 : ℝ) ^ ((A : ℝ) * interpolationScale q.1.numVars)⌉₊ *
          ((encLocalMapQuery q).length + 1) ^ e)
        (fun q => ((encLocalMapQuery q).length + 1) ^ b) :=
  exists_localMapPreimageCounter k

example (k : ℕ) :
    DecidableInSubexpTime (LocalMapHasPreimage k) encLocalMapQuery
      (fun q => q.1.numVars) :=
  decidableInSubexpTime_localMapHasPreimage k

example (k : ℕ) :
    ∃ (find : LocalMap × List Bool → Option (List Bool)) (A e b : ℕ),
      (∀ q : LocalMap × List Bool, find q = q.1.findPreimage k q.2) ∧
      (∀ (q : LocalMap × List Bool) (x : List Bool),
        find q = some x →
          q.1.Valid k = true ∧ x.length = q.1.numVars ∧ q.1.evalBits x = q.2) ∧
      (∀ q : LocalMap × List Bool, q.1.Valid k = true →
        ((find q).isSome = true ↔ 0 < q.1.preimageCount q.2)) ∧
      Turing.MultiTapeTM.ComputableInO find encLocalMapQuery
        (Turing.MultiTapeTM.encOption Turing.MultiTapeTM.encBits)
        (fun q => ⌈(2 : ℝ) ^ ((A : ℝ) * interpolationScale q.1.numVars)⌉₊ *
          ((encLocalMapQuery q).length + 1) ^ e)
        (fun q => ((encLocalMapQuery q).length + 1) ^ b) :=
  exists_localMapPreimageFinder k

end ComplexityTests.LocalMapCounting
