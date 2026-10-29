/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Parameterized.VertexCover.BussKernel

/-!
# Tests: Buss's polynomial kernel for vertex cover

Concrete instances exercising the high-degree rule, active-vertex relabelling, isolated-vertex
padding for exact-`k` covers, and rejection when `k > n`, `|high| > k`, or `|active| > k (k + 1)`.
-/

namespace ComplexityTests.VertexCoverKernel

open Cslib.Complexity Cslib.Complexity.VertexCover Cslib.Complexity.VertexCover.Buss
open Turing.MultiTapeTM

/-- A graph on `{10, 20, 30, 40, 50}` with target `k = 2`: vertex `10` has degree `3 > 2` (high),
vertices `20` and `30` share an edge (active low), and `40, 50` have no low neighbours (isolated
low). The kernel relabels `20, 30` to `0, 1`, pads with one isolated vertex `2` to reach
`numVertices = 3`, and reduces the target to `param = 1`. -/
private def sampleGraph : Graph :=
  ([10, 20, 30, 40, 50], [(10, 20), (10, 30), (10, 40), (20, 30)])

example :
    high (sampleGraph, 2) = [10] ∧
      low (sampleGraph, 2) = [20, 30, 40, 50] ∧
      active (sampleGraph, 2) = [20, 30] ∧
      param (sampleGraph, 2) = 1 ∧
      numVertices (sampleGraph, 2) = 3 ∧
      bussKernel (sampleGraph, 2) = (([0, 1, 2], [(0, 1), (1, 0)]), 1) ∧
      (sampleGraph, 2) ∈ VertexCover ∧
      bussKernel (sampleGraph, 2) ∈ VertexCover :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide,
    (search_eq_true_iff (sampleGraph, 2)).mp (by decide),
    (bussKernel_mem_iff (sampleGraph, 2)).mpr
      ((search_eq_true_iff (sampleGraph, 2)).mp (by decide))⟩

/-- A star on `{10, 20, 30, 40}` with centre `10` and target `k = 2`: removing the high centre `10`
leaves no active vertices (`active = []`) and reduced target `param = 1`, so one isolated low
vertex is kept as padding to witness the cover `{10, 20}` of size `2`. -/
private def starGraph : Graph :=
  ([10, 20, 30, 40], [(10, 20), (10, 30), (10, 40)])

example :
    active (starGraph, 2) = [] ∧
      bussKernel (starGraph, 2) = (([0], []), 1) ∧
      (starGraph, 2) ∈ VertexCover ∧
      bussKernel (starGraph, 2) ∈ VertexCover :=
  ⟨by decide, by decide,
    (search_eq_true_iff (starGraph, 2)).mp (by decide),
    (bussKernel_mem_iff (starGraph, 2)).mpr
      ((search_eq_true_iff (starGraph, 2)).mp (by decide))⟩

/-- Rejection when the number of high vertices exceeds `k`: for `k = 1`, the star on four vertices
has one high vertex, leaving `param = 0`, whereas two stars on `{0, 1, 2, 3, 4, 5}` with centres
`0` and `3` have two high vertices of degree `2 > 1`. -/
private def twoStars : Graph :=
  ([0, 1, 2, 3, 4, 5], [(0, 1), (0, 2), (3, 4), (3, 5)])

/-- Rejection when the number of active low vertices exceeds `k (k + 1)`: three disjoint edges with
`k = 1` have no high vertices (`degree = 1 ≤ 1`) and `6 > 1 * 2` active vertices. -/
private def threeEdges : Graph :=
  ([0, 1, 2, 3, 4, 5], [(0, 1), (2, 3), (4, 5)])

example :
    high (twoStars, 1) = [0, 3] ∧
      accept (twoStars, 1) = false ∧
      bussKernel (twoStars, 1) = noInstance ∧
      (twoStars, 1) ∉ VertexCover ∧
      high (threeEdges, 1) = [] ∧
      (active (threeEdges, 1)).length = 6 ∧
      accept (threeEdges, 1) = false ∧
      bussKernel (threeEdges, 1) = noInstance ∧
      (threeEdges, 1) ∉ VertexCover ∧
      bussKernel (starGraph, 5) = noInstance := by
  refine ⟨by decide, by decide, by decide, ?_, by decide, by decide, by decide, by decide, ?_,
    by decide⟩
  · rw [← bussKernel_mem_iff]
    exact noInstance_notMem
  · rw [← bussKernel_mem_iff]
    exact noInstance_notMem

/-! ### Plain automation over the kernel API -/

/-- Plain `fun_prop` composes the plain kernel certificates with plain hypotheses. -/
example {γ : Type} {enc : γ ↪ List Bool} {x : γ → Graph × ℕ} {G : γ → Graph} {v : γ → ℕ}
    (hx : ComputableInPolyTime x enc (encPair encGraph encNat))
    (hG : ComputableInPolyTime G enc encGraph) (hv : ComputableInPolyTime v enc encNat) :
    ComputableInPolyTime (fun c => high (x c)) enc (encList encNat) ∧
      ComputableInPolyTime (fun c => degree (G c) (v c)) enc encUnary := by
  refine ⟨?_, ?_⟩ <;> fun_prop

end ComplexityTests.VertexCoverKernel
