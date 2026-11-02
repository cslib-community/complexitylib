/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Algorithms.Lean.Karger.Memory

/-!
# Karger's contraction structure over memory on a triangle

The unit-weight triangle is laid out at address `0` with capacity `3`: size `3`, total `6`,
degrees `2, 2, 2`, then the matrix row by row. The tests check that this memory state satisfies
the invariant, evaluate the sampling query against `sampledPair` and a contraction against the
specification, and run a short client through the refinement. They instantiate the transferred
success bound `1 / 3`, the one-sided error and the cost bounds of Karger's algorithm over memory,
so that none of their hypotheses is vacuous.
-/

@[expose] public section

namespace ComplexityTests.KargerMemory

open scoped ENNReal
open Cslib Cslib.WeightedCut Cslib.DataStructure Cslib.Algorithms.Lean.Karger
  Cslib.Algorithms.Lean.Karger.Memory

/-- The triangle with unit weights. -/
def triangle : Fin 3 → Fin 3 → ℕ := fun i j => if i = j then 0 else 1

theorem isMultigraph_triangle : IsMultigraph triangle := ⟨by decide, by decide⟩

theorem minCut_triangle : 0 < minCut triangle :=
  (minCut_pos_iff (by simp) _).mpr (by unfold IsNonTrivialCut; decide)

/-- The layout at address `0` for at most three supervertices. -/
def L : Layout := ⟨0, 3⟩

/-- The triangle in memory: size, total, degrees, then the matrix. -/
def triangleMem : DataStructure.Memory.State :=
  ⟨fun a => [3, 6, 2, 2, 2, 0, 1, 1, 1, 0, 1, 1, 1, 0].getD a 0, 14⟩

/-- The memory state holds the triangle and satisfies the invariant at word size `8`. -/
theorem triangleMem_holds : abs L triangleMem = ⟨3, triangle⟩ ∧ Inv L 8 triangleMem :=
  abs_eq_and_inv isMultigraph_triangle (by decide) (by decide) (by decide) rfl (by decide)
    (by decide) (by decide) (by decide)

/-- The scans find the pair at offset `3`: row `1`, then column `2`, as `sampledPair` does. -/
example : (DataStructure.Memory.spec 8).clientResult triangleMem (pairAt L 3) = (1, 2) ∧
    sampledPair triangle 3 = (1, 2) :=
  ⟨by decide, sampledPair_eq (u := 1) (v := 2) (by decide)⟩

/-- The sampling query at every offset below the total answers `sampledPair` within
`2 · 3 + 1` memory units. -/
example (r : ℕ) (hr : r < 6) :
    (DataStructure.Memory.spec 8).wp DataStructure.Memory.charge (pairAt L r)
      (fun a s t => a = sampledPair triangle r ∧ s = triangleMem ∧ t ≤ 7) triangleMem := by
  have h := wp_pairAt triangleMem_holds.2 (r := r) (by rw [triangleMem_holds.1]; decide +revert)
  rw [triangleMem_holds.1] at h
  exact h

/-- Contracting `1` into `0` leaves two supervertices joined by weight `2`, of total `4`. -/
example :
    let s := (DataStructure.Memory.spec 8).clientState triangleMem (contract L 0 1)
    s.mem 0 = 2 ∧ s.mem 1 = 4 ∧ L.mat s.mem 0 1 = 2 ∧ L.mat s.mem 1 0 = 2 ∧
      L.mat s.mem 0 0 = 0 ∧ s.mem 2 = 2 ∧ s.mem 3 = 2 := by
  decide

/-- That contraction costs at most `7 · 3 + 7` memory units. -/
example : (DataStructure.Memory.spec 8).totalCost DataStructure.Memory.charge triangleMem
    ((DataStructure.Memory.spec 8).clientHistory triangleMem (contract L 0 1)) ≤ 28 := by
  decide

/-- Contract `1` into `0`, then read the total. -/
noncomputable def client : spec.Client ℕ := do
  let _ ← spec.call (.contract 0 1)
  spec.call .total

/-- The client is admissible on the triangle. -/
theorem validHistory_client :
    spec.ValidHistory ⟨3, triangle⟩ (spec.clientHistory ⟨3, triangle⟩ client) := by
  change valid ⟨3, triangle⟩ (.contract 0 1) ∧ valid (contractGraph ⟨3, triangle⟩ 0 1) .total ∧
    True
  exact ⟨⟨by decide, by decide, by decide⟩, trivial, trivial⟩

/-- Over memory, the client answers as on the specification. -/
example : (DataStructure.Memory.spec 8).clientResult triangleMem
    (link (refinement L 8).methods client) = spec.clientResult ⟨3, triangle⟩ client := by
  obtain ⟨-, h, -, -⟩ := (refinement L 8).simulates_client client triangleMem_holds.2
    (by rw [refinement_abs, triangleMem_holds.1]; exact validHistory_client)
  rwa [refinement_abs, triangleMem_holds.1] at h

/-- Over memory, it costs at most `(7 · 3 + 7) + 1` units. -/
example : (DataStructure.Memory.spec 8).totalCost DataStructure.Memory.charge triangleMem
    ((DataStructure.Memory.spec 8).clientHistory triangleMem
      (link (refinement L 8).methods client)) ≤ 29 := by
  have h := (amortized L 8).client client triangleMem_holds.2
    (by rw [refinement_abs, triangleMem_holds.1]; exact validHistory_client)
  rw [refinement_abs, triangleMem_holds.1] at h
  refine (Nat.le_add_right _ _).trans (h.trans ?_)
  decide

/-- Karger's algorithm over memory finds the minimum cut of the triangle with probability at
least `1 / 3`. -/
example : (2 : ℝ≥0∞) / ((3 * (3 - 1) : ℕ) : ℝ≥0∞) ≤
    ((DataStructure.Memory.spec 8).toRandomized.withCoins.run (kargerProg L 8)
      triangleMem).toOuterMeasure {x | x.1 = minCut triangle} :=
  two_div_le_toOuterMeasure_kargerProg triangleMem_holds.2 triangleMem_holds.1 (by norm_num)
    isMultigraph_triangle minCut_triangle

/-- Every answer is at least the minimum cut weight. -/
example {x : ℕ × DataStructure.Memory.State}
    (hx : x ∈ ((DataStructure.Memory.spec 8).toRandomized.withCoins.run (kargerProg L 8)
      triangleMem).support) :
    minCut triangle ≤ x.1 :=
  minCut_le_of_mem_support_kargerProg triangleMem_holds.2 triangleMem_holds.1 (by norm_num)
    isMultigraph_triangle hx

/-- The expected memory cost is at most `1 · (1 + 4 · 28) + 2 · 28 = 169` units. -/
example : (DataStructure.Memory.spec 8).toRandomized.withCoins.expectedCost
    ((DataStructure.Memory.spec 8).toRandomized.coinCharge (fun _ => 1) DataStructure.Memory.charge)
    (kargerProg L 8) triangleMem ≤ (169 : ℕ) :=
  expectedCost_kargerProg_le triangleMem_holds.2 triangleMem_holds.1 (by norm_num)
    isMultigraph_triangle

/-- It draws at most one coin in expectation. -/
example : (DataStructure.Memory.spec 8).toRandomized.withCoins.expectedCost
    ((DataStructure.Memory.spec 8).toRandomized.coinCharge (fun _ => 1) fun _ _ => 0)
    (kargerProg L 8) triangleMem ≤ (1 : ℕ) :=
  expectedCoins_kargerProg_le triangleMem_holds.2 triangleMem_holds.1 (by norm_num)
    isMultigraph_triangle

/-- The exported bound applies to the triangle. -/
example : ∃ F : ℕ → ℕ, (DataStructure.Memory.spec 8).toRandomized.withCoins.expectedCost
    ((DataStructure.Memory.spec 8).toRandomized.coinCharge (fun _ => 1) DataStructure.Memory.charge)
    (kargerProg L 8) triangleMem ≤ (F 3 : ℝ≥0∞) :=
  let ⟨F, _, hF⟩ := exists_expectedCost_kargerProg_isBigO
  ⟨F, hF triangleMem_holds.2 triangleMem_holds.1 rfl (by norm_num) isMultigraph_triangle⟩

end ComplexityTests.KargerMemory
