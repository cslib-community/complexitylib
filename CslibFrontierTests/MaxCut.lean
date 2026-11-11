/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Complexity.Problems.MaxCut

/-!
# Weighted maximum cut: tests

Cut weights on small weighted multigraphs (self-loops, parallel edges, zero weights), the
verifier on accepted and rejected certificates, Karp's reduction from `Partition` on yes and no
instances, and compositional `fun_prop` synthesis.
-/

namespace CslibFrontierTests.MaxCut

open Cslib.Complexity Turing.MultiTapeTM

/-! ### Headline results -/

example : MaxCut ∈ NP encMaxCut ∧
    PolyTimeReducible (encList encNat) encMaxCut Partition MaxCut :=
  ⟨MaxCut_npComplete.1, polyTimeReducible_Partition_MaxCut⟩

example : PolyTimeReducible encSubsetSum encMaxCut SubsetSum MaxCut :=
  polyTimeReducible_SubsetSum_Partition.trans polyTimeReducible_Partition_MaxCut

/-! ### Cut weights -/

-- The triangle with weights 2, 3 and 4: cutting off vertex `2` cuts the edges of weight 3 and 4.
example : MaxCut.cutWeight [⟨0, 1, 2⟩, ⟨1, 2, 3⟩, ⟨0, 2, 4⟩] (fun v => v == 2) = 7 := rfl
example : MaxCut.cutWeight [⟨0, 1, 2⟩, ⟨1, 2, 3⟩, ⟨0, 2, 4⟩] (fun v => v == 0) = 6 := rfl
-- The trivial cuts cut nothing.
example : MaxCut.cutWeight [⟨0, 1, 2⟩, ⟨1, 2, 3⟩, ⟨0, 2, 4⟩] (fun _ => true) = 0 := rfl
example : MaxCut.cutWeight [⟨0, 1, 2⟩, ⟨1, 2, 3⟩, ⟨0, 2, 4⟩] (fun _ => false) = 0 := rfl

-- Self-loops never cross; parallel edges add their weights.
example : MaxCut.cutWeight [⟨0, 0, 5⟩] (fun v => v == 0) = 0 := rfl
example : MaxCut.cutWeight [⟨0, 1, 5⟩, ⟨1, 0, 6⟩] (fun v => v == 0) = 11 := rfl

example : (⟨[⟨0, 1, 2⟩, ⟨1, 2, 3⟩, ⟨0, 2, 4⟩], 7⟩ : MaxCutInstance) ∈ MaxCut := ⟨{2}, by decide⟩
example : (⟨[⟨0, 0, 5⟩], 0⟩ : MaxCutInstance) ∈ MaxCut := ⟨∅, le_refl 0⟩
example : (⟨[⟨0, 0, 5⟩], 1⟩ : MaxCutInstance) ∉ MaxCut := by
  rintro ⟨S, hS⟩
  simp [MaxCut.cutWeight, MaxCut.crosses] at hS

/-! ### The verifier -/

-- The endpoints are `[0, 1, 1, 2, 0, 2]`; the mask selects the distinct entry `2`.
example : MaxCut.verifier (⟨[⟨0, 1, 2⟩, ⟨1, 2, 3⟩, ⟨0, 2, 4⟩], 7⟩,
    [false, false, false, true, false, false]) = true := by decide
-- Cutting off vertex `0` has weight 6 only.
example : MaxCut.verifier (⟨[⟨0, 1, 2⟩, ⟨1, 2, 3⟩, ⟨0, 2, 4⟩], 7⟩,
    [true, false, false, false, false, false]) = false := by decide
-- Large weights are added and compared in binary.
example : MaxCut.verifier (⟨[⟨0, 1, 2 ^ 80⟩, ⟨1, 2, 2 ^ 80⟩], 2 ^ 81⟩, [false, true]) =
    true := by decide

/-! ### Karp's reduction from `Partition` -/

-- The complete graph on three positions, weighted by products, with bound `⌈36 / 4⌉ = 9`.
example : Partition.toMaxCut [1, 2, 3] = ⟨[⟨0, 1, 2⟩, ⟨0, 2, 3⟩, ⟨1, 2, 6⟩], 9⟩ := by
  decide

-- `[1, 2, 3]` splits as `{1, 2}`, `{3}`; the cut off position `2` has weight `3 * 3 = 9`.
example : Partition.toMaxCut [1, 2, 3] ∈ MaxCut := ⟨{2}, by decide⟩
example : [1, 2, 3] ∈ Partition :=
  (Partition.toMaxCut_mem_iff _).1 ⟨{2}, by decide⟩

-- `[1, 2]` has odd total; its best cut has weight `2 < ⌈9 / 4⌉ = 3`.
example : Partition.toMaxCut [1, 2] = ⟨[⟨0, 1, 2⟩], 3⟩ := by decide
example : Partition.toMaxCut [1, 2] ∉ MaxCut := fun h => by
  obtain ⟨s, hs, hsum⟩ := mem_Partition_iff_sublist.1 ((Partition.toMaxCut_mem_iff _).1 h)
  exact absurd (⟨s, List.mem_sublists.2 hs, hsum⟩ : ∃ s ∈ [1, 2].sublists, 2 * s.sum = 3)
    (by decide)

-- `[2, 2]` splits with product `4 = ⌈16 / 4⌉`; `[1, 3]` reaches only `3 < 4`.
example : Partition.toMaxCut [2, 2] = ⟨[⟨0, 1, 4⟩], 4⟩ := by decide
example : Partition.toMaxCut [1, 3] = ⟨[⟨0, 1, 3⟩], 4⟩ := by decide
example : Partition.toMaxCut [1, 3] ∉ MaxCut := fun h => by
  obtain ⟨s, hs, hsum⟩ := mem_Partition_iff_sublist.1 ((Partition.toMaxCut_mem_iff _).1 h)
  exact absurd (⟨s, List.mem_sublists.2 hs, hsum⟩ : ∃ s ∈ [1, 3].sublists, 2 * s.sum = 4)
    (by decide)

-- The empty list partitions trivially, and the empty graph meets the bound `0`.
example : Partition.toMaxCut [] = ⟨[], 0⟩ := rfl
example : Partition.toMaxCut [] ∈ MaxCut := ⟨∅, le_refl 0⟩

/-! ### Compositional `fun_prop` synthesis -/

example : ComputableInPolyTime (fun a : List ℕ => Partition.toMaxCut (a ++ a))
    (encList encNat) encMaxCut := by fun_prop

example : ComputableInPolyTime
    (fun x : MaxCutInstance =>
      (⟨x.edges.map fun e => ⟨e.v, e.u, e.weight⟩, x.bound⟩ : MaxCutInstance))
    encMaxCut encMaxCut := by fun_prop

end CslibFrontierTests.MaxCut

-- Global `fun_prop` availability without opening `Cslib.Complexity` or `Cslib.Complexity.MaxCut`.
example : Turing.MultiTapeTM.ComputableInPolyTime
    (fun x : Cslib.Complexity.MaxCutInstance =>
      Cslib.Complexity.MaxCutInstance.mk
        (x.edges.map fun e => Cslib.Complexity.MaxCut.WeightedEdge.mk e.u e.v e.weight)
        x.bound)
    Cslib.Complexity.encMaxCut Cslib.Complexity.encMaxCut := by
  fun_prop
