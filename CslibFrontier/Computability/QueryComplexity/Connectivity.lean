/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.DecisionTree.Basic
public import CslibFrontier.Foundations.Data.BitString.Graph
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import CslibFrontier.Foundations.Combinatorics.SimpleGraph.Connectivity.Bridges
import CslibFrontier.Foundations.Data.BitString.PartialAssignment

/-!
# Graph connectivity requires every edge query

The total connectivity function on labelled undirected simple graphs has deterministic query
complexity `n.choose 2`, one query per possible edge [AroraBarak07] (public draft, Theorem 11.4).
Queries may be
repeated. The bridge adversary answers false unless deleting the queried edge disconnects the
remaining possible graph; confirmed edges remain bridges of that graph.

The empty graph is disconnected and the one-vertex graph is connected, following Mathlib's
conventions. Both functions have zero query complexity.

## Main definitions

* `Cslib.BitString.Graph.connectivity`: the total labelled simple-graph connectivity function.

## Main results

* `Cslib.BitString.Graph.complexity_connectivity`: its exact deterministic query complexity.
* `Cslib.BitString.Graph.connectivity_zero`, `connectivity_one`: the empty and singleton cases.

## References

* [S. Arora and B. Barak, *Computational Complexity: A Modern Approach*, public draft,
  Theorem 11.4][AroraBarak07]
-/

public section

namespace Cslib.BitString.Graph

/-- Whether the graph encoded by the edge bits is connected. The vertex set is all of `Fin n`,
including isolated vertices. -/
noncomputable def connectivity (n : ℕ) : BooleanFunction (edgeCount n) :=
  fun x => @decide ((graph x).Connected) (Classical.propDecidable _)

@[simp] theorem connectivity_eq_true {n : ℕ} {x : BitString (edgeCount n)} :
    connectivity n x = true ↔ (graph x).Connected := by
  simp [connectivity]

@[simp] theorem connectivity_zero (x : BitString (edgeCount 0)) : connectivity 0 x = false := by
  simp [connectivity, SimpleGraph.connected_iff]

@[simp] theorem connectivity_one (x : BitString (edgeCount 1)) : connectivity 1 x = true :=
  connectivity_eq_true.mpr SimpleGraph.Connected.of_subsingleton

private def lowerGraph {n : ℕ} (ρ : PartialAssignment (Fin (edgeCount n))) :
    SimpleGraph (Fin n) := graph (ρ.fill fun _ => false)

private def upperGraph {n : ℕ} (ρ : PartialAssignment (Fin (edgeCount n))) :
    SimpleGraph (Fin n) := graph (ρ.fill fun _ => true)

private theorem lowerGraph_le_upperGraph {n : ℕ} (ρ : PartialAssignment (Fin (edgeCount n))) :
    lowerGraph ρ ≤ upperGraph ρ := by
  apply graph_mono
  intro i hi
  cases h : ρ i <;> simp_all [PartialAssignment.fill]

private theorem free_card_le_depth {n : ℕ} (t : DecisionTree (Fin (edgeCount n)) Bool)
    (ρ : PartialAssignment (Fin (edgeCount n)))
    (ht : ∀ x, ρ.Agrees x → t.eval x = connectivity n x)
    (hU : (upperGraph ρ).Connected)
    (hbridge : ∀ e ∈ (lowerGraph ρ).edgeSet, (upperGraph ρ).IsBridge e) :
    ρ.free.card ≤ t.depth := by
  classical
  induction t generalizing ρ with
  | leaf b =>
    have heval : connectivity n (ρ.fill fun _ => false) =
        connectivity n (ρ.fill fun _ => true) :=
      (ht (ρ.fill fun _ => false) (ρ.agrees_fill _)).symm.trans
        (ht (ρ.fill fun _ => true) (ρ.agrees_fill _))
    have hL : (lowerGraph ρ).Connected := connectivity_eq_true.mp
      (heval.trans (connectivity_eq_true.mpr hU))
    have heq : lowerGraph ρ = upperGraph ρ :=
      hL.preconnected.eq_of_forall_isBridge (lowerGraph_le_upperGraph ρ) hbridge
    have hwords := graph_injective heq
    have hfree : ρ.free = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      have h := congrFun hwords i
      simp [PartialAssignment.fill, PartialAssignment.mem_free.mp hi] at h
    simp [hfree]
  | node i left right ihl ihr =>
    have hdepthl : left.depth ≤ (DecisionTree.node i left right).depth := by
      simp only [DecisionTree.depth_node]; omega
    have hdepthr : right.depth ≤ (DecisionTree.node i left right).depth := by
      simp only [DecisionTree.depth_node]; omega
    cases hρi : ρ i with
    | some b =>
      have hquery (x) (hx : ρ.Agrees x) : x i = b := hx i b hρi
      cases b with
      | false =>
        apply (ihl ρ (fun x hx => ?_) hU hbridge).trans hdepthl
        simpa only [DecisionTree.eval_node, hquery x hx, Bool.cond_false] using ht x hx
      | true =>
        apply (ihr ρ (fun x hx => ?_) hU hbridge).trans hdepthr
        simpa only [DecisionTree.eval_node, hquery x hx, Bool.cond_true] using ht x hx
    | none =>
      have hi : i ∈ ρ.free := PartialAssignment.mem_free.mpr hρi
      have hbranch (b : Bool) (x) (hx : PartialAssignment.Agrees (Function.update ρ i (some b)) x) :
          (cond b right left).eval x = connectivity n x := by
        have hxi : x i = b := hx i b (Function.update_self _ _ _)
        have hxρ : ρ.Agrees x := ((PartialAssignment.Extends.refl ρ).update_some hi b).agrees hx
        cases b <;> simpa only [DecisionTree.eval_node, hxi, Bool.cond_false, Bool.cond_true]
          using ht x hxρ
      let e : Edge n := (edgeEquiv n).symm i
      by_cases hb : (upperGraph ρ).IsBridge e.1
      · have hUeq : upperGraph (Function.update ρ i (some true)) = upperGraph ρ := by
          simp only [upperGraph, PartialAssignment.fill_update]
          rw [Function.update_eq_self_iff.mpr
            (PartialAssignment.fill_of_eq_none hρi (fun _ => true)).symm]
        have hB : ∀ a ∈ (lowerGraph (Function.update ρ i (some true))).edgeSet,
            (upperGraph (Function.update ρ i (some true))).IsBridge a := by
          intro a ha
          rw [hUeq]
          have hdiag := (lowerGraph (Function.update ρ i (some true))).not_isDiag_of_mem_edgeSet ha
          have hbit := (mem_edgeSet_graph _ ⟨a, hdiag⟩).mp ha
          change PartialAssignment.fill (Function.update ρ i (some true)) (fun _ => false)
            (edgeEquiv n ⟨a, hdiag⟩) = true at hbit
          rw [PartialAssignment.fill_update] at hbit
          by_cases hai : edgeEquiv n ⟨a, hdiag⟩ = i
          · have hae : a = e.1 := congrArg Subtype.val
              ((edgeEquiv n).injective (hai.trans (Equiv.apply_symm_apply _ _).symm))
            exact hae ▸ hb
          · rw [Function.update_of_ne hai] at hbit
            exact hbridge a ((mem_edgeSet_graph _ ⟨a, hdiag⟩).mpr hbit)
        have hbound := ihr _ (hbranch true) (hUeq ▸ hU) hB
        rw [PartialAssignment.free_update] at hbound
        have hcard := Finset.card_erase_add_one hi
        simp only [DecisionTree.depth_node]
        omega
      · have hUeq : upperGraph (Function.update ρ i (some false)) =
            (upperGraph ρ).deleteEdges {e.1} := by
          simp only [upperGraph, PartialAssignment.fill_update, graph_update_false, e]
        have hLeq : lowerGraph (Function.update ρ i (some false)) = lowerGraph ρ := by
          simp only [lowerGraph, PartialAssignment.fill_update]
          rw [Function.update_eq_self_iff.mpr
            (PartialAssignment.fill_of_eq_none hρi (fun _ => false)).symm]
        have hconn : (upperGraph (Function.update ρ i (some false))).Connected := by
          rw [hUeq]
          exact hU.preconnected.connected_deleteEdges_of_not_isBridge hb
        have hB : ∀ a ∈ (lowerGraph (Function.update ρ i (some false))).edgeSet,
            (upperGraph (Function.update ρ i (some false))).IsBridge a := by
          intro a ha
          rw [hLeq] at ha
          rw [hUeq]
          exact (hbridge a ha).anti (SimpleGraph.deleteEdges_le _)
        have hbound := ihl _ (hbranch false) hconn hB
        rw [PartialAssignment.free_update] at hbound
        have hcard := Finset.card_erase_add_one hi
        simp only [DecisionTree.depth_node]
        omega

/-- **Connectivity is evasive:** deciding connectivity of a labelled undirected simple graph
requires every possible edge in the worst case [AroraBarak07] (public draft, Theorem 11.4). -/
theorem complexity_connectivity (n : ℕ) :
    DecisionTree.complexity (connectivity n) = n.choose 2 := by
  classical
  apply le_antisymm
  · simpa only [Fintype.card_fin, edgeCount_eq_choose] using
      DecisionTree.complexity_le_card (connectivity n)
  · rw [← edgeCount_eq_choose]
    apply DecisionTree.le_complexity_iff.mpr
    intro t ht
    by_cases hn : n = 0
    · subst n
      simp
    · have : NeZero n := ⟨hn⟩
      have hU : (upperGraph (PartialAssignment.empty :
          PartialAssignment (Fin (edgeCount n)))).Connected := by
        simp [upperGraph]
      have hB : ∀ e ∈ (lowerGraph (PartialAssignment.empty :
          PartialAssignment (Fin (edgeCount n)))).edgeSet,
          (upperGraph (PartialAssignment.empty :
            PartialAssignment (Fin (edgeCount n)))).IsBridge e := by
        simp [lowerGraph]
      simpa only [PartialAssignment.free_empty, Finset.card_univ, Fintype.card_fin] using
        free_card_le_depth t PartialAssignment.empty (fun x _ => ht x) hU hB

end Cslib.BitString.Graph
