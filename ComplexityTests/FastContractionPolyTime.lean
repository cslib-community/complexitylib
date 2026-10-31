/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.CountingSimulation.FastAlgorithm

/-! # The components of the native contraction recursion in polynomial time: checked instances

The caps on the rows and the exponents, the schedule's quantities on a call that is not active,
and the instance of the contraction interface from the resource analysis alone. -/

namespace ComplexityTests.FastContractionPolyTime

open Turing.MultiTapeTM Cslib.Circuits.Frontier Cslib.Circuits.Frontier.FastContraction
  Cslib.Circuits.Frontier.ContractionSchedule Cslib.Complexity.CountingSimulation

/-- One row `0` and one column `1` joined by edge `0`, with full tables. -/
def tiny : ExplicitTensorNetwork ℕ := ⟨1, [([0], [1, 2]), ([0], [3, 4])]⟩

-- The number of rows is stored in binary, so a call may claim `2 ^ 100` rows; the cap keeps the
-- two vertices, and on the rows-first root it is inactive.
example : rowCap (root (3, 2 ^ 100, tiny)) = 2 := by decide
example : rowCap (root (3, 1, tiny)) = 1 := by decide

-- The packing of the root: one packet of `2 ^ 0` slots, within the bound `M (2 ^ a) ^ 12`.
example : slots (root (3, 1, tiny)) = 0 := by decide
example : (packing (root (3, 1, tiny))).2.1 = 1 := by decide
example : (packing (root (3, 1, tiny))).2.1 ≤
    (root (3, 1, tiny)).edges * (2 ^ slots (root (3, 1, tiny))) ^ 12 :=
  NativeChild.numPackets_nativeParentPacking_le _ _ _

-- On every call, `2 ^ a ≤ s + 1`, and the levels are at most `a + 1`.
example (x : Call) : 2 ^ slots x ≤ x.scale + 1 := two_pow_slots_le x
example (x : Call) (k : ℕ) : level x k ≤ slots x + 1 := level_le x k

-- The cap on the exponents leaves the tuples of weight below the budget unchanged.
example : ([1, 0, 1] : List ℕ).map (min · 3) = [1, 0, 1] :=
  map_min_of_mem_budgetTuples (ws := [1, 1, 1]) (by decide) (by decide)

-- The components of the scheme of the native child builder are polynomial-time.
example : (scheme nativeMk).PolyTime encCall encFrame encValue := scheme_nativeMk_polyTime

-- The contraction interface for admissible explicit networks, from the resource analysis alone.
noncomputable example (hana : FastAnalysis nativeMk) :
    ContractionAlgorithm (encPair encNat ExplicitTensorNetwork.encExplicitNetwork)
      (fun G => G.2.contraction) ExplicitAdmissible :=
  contractionAlgorithmOfNative hana

end ComplexityTests.FastContractionPolyTime
