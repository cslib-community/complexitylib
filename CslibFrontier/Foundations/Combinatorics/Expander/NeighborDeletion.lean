/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, finite unions and simple-graph neighborhood bounds)

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Basic.Real.Basic

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Neighborhood expansion after deleting edges

Deleting an incidence from a chosen vertex set can remove at most one of its neighbors. More
precisely, the number of incidences minus the size of their union cannot increase under deletion.
Consequently, passing from a regular graph of degree `D` to a spanning regular subgraph of
positive degree `a` transfers a lossless expansion bound with loss `ε` to loss `ε * D / a`,
without changing the cutoff on the size of the vertex set.

The finite-set and graph inequalities also apply to irregular graphs. The pointwise expansion
bound needs degree assumptions only on the chosen set, so it applies separately to either side
of a biregular bipartite graph without introducing another bipartite graph type.

## Main results

* `Finset.card_biUnion_le_card_biUnion_add_sum_card_sdiff`: the loss in a union is bounded by
  the sum of the losses in its constituent sets.
* `SimpleGraph.card_neighborBiUnion_add_sum_degree_le`: deleting edges does not increase
  the number of incidences minus the number of distinct neighbors.
* `SimpleGraph.neighborBiUnion_loss_bound_of_le`: the resulting expansion bound on one set,
  with degree assumptions restricted to that set.
* `SimpleGraph.lossless_bound_of_le_of_isRegularOfDegree`: the loss `ε * D / a` for a regular
  spanning subgraph, on the same range of set sizes as the original graph.

These are direct counting lemmas. They do not construct a regular subgraph or certify the rank
of an adjacency matrix.
-/

public section

open Finset
open scoped BigOperators

namespace Finset

/-- Replacing each member of a finite family loses at most the sum of the individual set losses
from its union. No containment assumption on the replacement sets is needed. -/
theorem card_biUnion_le_card_biUnion_add_sum_card_sdiff
    {ι α : Type*} [DecidableEq α] (s : Finset ι) (A B : ι → Finset α) :
    #(s.biUnion A) ≤ #(s.biUnion B) + ∑ i ∈ s, #(A i \ B i) := by
  have hsub : s.biUnion A ⊆ s.biUnion B ∪ s.biUnion (fun i ↦ A i \ B i) := by
    intro x hx
    obtain ⟨i, hi, hx⟩ := mem_biUnion.mp hx
    by_cases hb : x ∈ B i
    · exact mem_union_left _ (mem_biUnion.mpr ⟨i, hi, hb⟩)
    · exact mem_union_right _ (mem_biUnion.mpr ⟨i, hi, mem_sdiff.mpr ⟨hx, hb⟩⟩)
  calc
    #(s.biUnion A) ≤ #(s.biUnion B ∪ s.biUnion (fun i ↦ A i \ B i)) := card_le_card hsub
    _ ≤ #(s.biUnion B) + #(s.biUnion (fun i ↦ A i \ B i)) := card_union_le _ _
    _ ≤ #(s.biUnion B) + ∑ i ∈ s, #(A i \ B i) :=
      Nat.add_le_add_left card_biUnion_le _

end Finset

namespace SimpleGraph

variable {V : Type*} [DecidableEq V] {G H : SimpleGraph V}
variable [G.LocallyFinite] [H.LocallyFinite]

/-- In a spanning subgraph, the number of incidences from `S` minus the number of distinct
neighbors cannot exceed that of the original graph. The additive form avoids subtraction in
the natural numbers and also covers irregular graphs. -/
theorem card_neighborBiUnion_add_sum_degree_le (hHG : H ≤ G) (S : Finset V) :
    #(S.biUnion (fun v ↦ G.neighborFinset v)) + ∑ v ∈ S, H.degree v ≤
      #(S.biUnion (fun v ↦ H.neighborFinset v)) + ∑ v ∈ S, G.degree v := by
  have hsub (v : V) : H.neighborFinset v ⊆ G.neighborFinset v := by
    intro w hw
    exact (G.mem_neighborFinset v w).2 (hHG ((H.mem_neighborFinset v w).1 hw))
  have hsum :
      (∑ v ∈ S, #(G.neighborFinset v \ H.neighborFinset v)) +
          ∑ v ∈ S, H.degree v =
        ∑ v ∈ S, G.degree v := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun v _ ↦ card_sdiff_add_card_eq_card (hsub v)
  calc
    #(S.biUnion (fun v ↦ G.neighborFinset v)) + ∑ v ∈ S, H.degree v ≤
        (#(S.biUnion (fun v ↦ H.neighborFinset v)) +
          ∑ v ∈ S, #(G.neighborFinset v \ H.neighborFinset v)) +
            ∑ v ∈ S, H.degree v :=
      Nat.add_le_add_right
        (card_biUnion_le_card_biUnion_add_sum_card_sdiff S
          (fun v ↦ G.neighborFinset v) (fun v ↦ H.neighborFinset v)) _
    _ = #(S.biUnion (fun v ↦ H.neighborFinset v)) + ∑ v ∈ S, G.degree v := by
      rw [Nat.add_assoc, hsum]

/-- An expansion bound survives deletion with unchanged absolute loss `ε * D * S.card`.
Only the degrees of vertices in `S` are prescribed, allowing this theorem to be applied on
one side of a biregular graph. This form also allows the remaining degree `a` to be zero. -/
theorem neighborBiUnion_loss_bound_of_le (hHG : H ≤ G) {S : Finset V} {D a : ℕ} {ε : ℝ}
    (hG : ∀ v ∈ S, G.degree v = D) (hH : ∀ v ∈ S, H.degree v = a)
    (hexpand : (1 - ε) * D * S.card ≤ ((S.biUnion (fun v ↦ G.neighborFinset v)).card : ℝ)) :
    ((a : ℝ) - ε * D) * S.card ≤ ((S.biUnion (fun v ↦ H.neighborFinset v)).card : ℝ) := by
  have hsumG : (∑ v ∈ S, G.degree v) = S.card * D := by
    calc
      _ = ∑ _v ∈ S, D := sum_congr rfl hG
      _ = _ := by simp
  have hsumH : (∑ v ∈ S, H.degree v) = S.card * a := by
    calc
      _ = ∑ _v ∈ S, a := sum_congr rfl hH
      _ = _ := by simp
  have hcard := card_neighborBiUnion_add_sum_degree_le hHG S
  rw [hsumG, hsumH] at hcard
  have hcast :
      ((S.biUnion (fun v ↦ G.neighborFinset v)).card : ℝ) + S.card * a ≤
        ((S.biUnion (fun v ↦ H.neighborFinset v)).card : ℝ) + S.card * D := by
    exact_mod_cast hcard
  calc
    ((a : ℝ) - ε * D) * S.card =
        (1 - ε) * D * S.card + S.card * a - S.card * D := by ring
    _ ≤ ((S.biUnion (fun v ↦ G.neighborFinset v)).card : ℝ) + S.card * a - S.card * D :=
      sub_le_sub_right (add_le_add hexpand le_rfl) _
    _ ≤ ((S.biUnion (fun v ↦ H.neighborFinset v)).card : ℝ) := sub_le_iff_le_add.mpr hcast

/-- A positive-degree regular spanning subgraph preserves the original cutoff `K` for
lossless expansion, with loss changed from `ε` to `ε * D / a`. The theorem assumes the
subgraph is given; it makes no existence, explicitness, or adjacency-rank assertion. -/
theorem lossless_bound_of_le_of_isRegularOfDegree (hHG : H ≤ G) {D a K : ℕ} {ε : ℝ}
    (hG : G.IsRegularOfDegree D) (hH : H.IsRegularOfDegree a) (ha : 0 < a)
    (hexpand : ∀ S : Finset V, S.card ≤ K →
      (1 - ε) * D * S.card ≤ ((S.biUnion (fun v ↦ G.neighborFinset v)).card : ℝ)) :
    ∀ S : Finset V, S.card ≤ K →
      (1 - ε * D / a) * a * S.card ≤ ((S.biUnion (fun v ↦ H.neighborFinset v)).card : ℝ) := by
  intro S hS
  have ha' : (a : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt ha)
  rw [sub_mul, one_mul, div_mul_cancel₀ _ ha']
  exact neighborBiUnion_loss_bound_of_le hHG (fun v _ ↦ hG v) (fun v _ ↦ hH v)
    (hexpand S hS)

end SimpleGraph
