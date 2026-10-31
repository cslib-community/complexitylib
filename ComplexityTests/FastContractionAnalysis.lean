/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.CountingSimulation.FastAnalysis

/-! # The resource analysis of the native recursion: checked instances

The derivation invariant and the shape invariant at a small root, the reduced values, the clock
arithmetic at a concrete size, and the statement of the remaining obligation. -/

namespace ComplexityTests.FastContractionAnalysis

open Cslib.Circuits.Frontier Cslib.Circuits.Frontier.FastContraction
  Cslib.Complexity.CountingSimulation Cslib.Circuits.Frontier.ContractionSchedule

/-- One row `0` and one column `1` joined by edge `0`, with full tables. -/
def tiny : ℕ × ExplicitTensorNetwork ℕ := (1, ⟨1, [([0], [1, 2]), ([0], [3, 4])]⟩)

example : fastGuard tiny = true := by decide

/-- The root of `tiny` at precision `3`. -/
abbrev tinyRoot : Call := root (ExplicitTensorNetwork.capPrecision (3, tiny))

-- The root is reached, and it is the only reached call at depth `0`.
example : Reach nativeMk tinyRoot tinyRoot := .root
example (x : Call) (hx : Reach nativeMk tinyRoot x) (h0 : x.depth = 0) : x = tinyRoot :=
  hx.eq_root_of_depth_le (by rw [h0]; rfl)

-- The root is a leaf, so its derivation has one node and no open call.
example : active tinyRoot = false := by decide

-- The shape invariant holds at every reached call; at the root it is the root itself.
example : Shape tinyRoot tinyRoot :=
  Reach.shape rfl rfl (wf_root 3 (by decide)) .root

-- The root is on the schedule for `C = 3`: its precision `3` is at most `3 ⬝ 1`.
example : OnSchedule 3 tiny.2.numEdges tinyRoot :=
  onSchedule_root_capPrecision (by decide) (by norm_num) (by decide)

-- Values are reduced at their precision: at most `e` coordinates below `2 ^ p`.
example : ReducedAt tinyRoot.prec tinyRoot.fl (value nativeMk tinyRoot) :=
  reducedAt_value nativeMk tinyRoot

-- The modulus at `m = 1` has `2 ⬝ 3 ^ 1 = 6` coefficients, within `32 (m + 1) ^ 2`.
example : (modulus 1).length = 6 := by decide
example : (modulus 1).length ≤ 32 * (1 + 1) ^ 2 := length_modulus_le 1

-- The clock arithmetic: with `m = 100` edges, precision `p = 50 ≤ 1 ⬝ m` and `D = 1`, a derivation
-- within the call count of `C' = ⌊50 / 100⌋ + 1 = 1` fits in the clock.
example (N : ℕ) (hN : N ≤ 2 ^ ((245760 * (50 / 100 + 1) + 37) * 100 / Nat.sqrt (Nat.log 2 100))) :
    2 * N - 1 ≤ 2 ^ (fuelConst * (100 + 50) / Nat.sqrt (Nat.log 2 (100 + 50))) :=
  two_mul_sub_one_le_fuel (D := 1) (by norm_num) (by norm_num) hN

-- A child of a parent with `M` edges under (D.6) has at most `M / 16` edges.
example {r a i Δ : ℕ} {D : DescribedNetwork VertexDesc} (hD : D.IsRowsFirstBipartite r)
    (hK : 64 ^ a ≤ D.numEdges) (hia : i < a) (hdeg : ∀ v ∈ D.vertices, v.1.length ≤ Δ)
    (hM : 2 * Δ * (64 ^ (2 * a)) ^ 2 ≤ D.numEdges) (fl : List ℕ) (pt : ℕ) (t : ℤ)
    (ζ β : List ℕ) (g : Fin 64) :
    16 * (NativeChild.nativeChild fl a i pt t ζ r D (NativeChild.nativeParentPacking r a D) β
      g).numEdges ≤ D.numEdges :=
  NativeChild.sixteen_mul_numEdges_nativeChild_le hD hK hia hdeg hM fl pt t ζ β g

-- The sizes are proved; the resource analysis needs only the leaf bounds.
example : FastSizes := fastSizes
example (hL : FastLeaves) : FastAnalysis nativeMk := fastAnalysis_nativeMk hL

end ComplexityTests.FastContractionAnalysis
