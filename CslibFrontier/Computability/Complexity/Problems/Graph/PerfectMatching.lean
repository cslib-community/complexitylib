/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.Matching.Positions
public import CslibFrontier.Logics.Propositional.CSP.ExactlyOne
import CslibFrontier.Foundations.Data.List.Range
import Mathlib.Data.List.GetD

/-!
# Perfect matchings as an exactly-one instance

The perfect matchings of the graph `G.induced` of a vertex and edge list `G : Graph` are the
models of a Holant instance (`Cslib.Complexity.Graph.perfectMatchingInstance`): one Boolean
variable for each edge, and one exactly-one constraint for each vertex on its incident edges. The
edges are listed by `Cslib.Complexity.Graph.edgeList`, which keeps the edges of `G` between
distinct declared vertices and erases repetitions in either orientation, so that its positions
are the edges of `G.induced`. The exactly-one partition function of the instance is the number of
perfect matchings (`Cslib.Complexity.Graph.partitionFunction_perfectMatchingInstance`).

Every variable occurs in the constraints of the two ends of its edge
(`Cslib.Complexity.Graph.count_vars_perfectMatchingInstance`), and the constraint of a vertex has
at most as many variables as the vertex has neighbours
(`Cslib.Complexity.Graph.length_le_of_mem_perfectMatchingInstance`).

## Main definitions

* `Cslib.Complexity.Graph.edgeList`: the edges of `G.induced`, each listed once.
* `Cslib.Complexity.Graph.perfectMatchingInstance`: the perfect-matching instance.

## Main results

* `Cslib.Complexity.Graph.partitionFunction_perfectMatchingInstance`: its exactly-one partition
  function is the number of perfect matchings of `G.induced`.
* `Cslib.Complexity.Graph.count_vars_perfectMatchingInstance`: each variable occurs at most twice.
* `Cslib.Complexity.Graph.length_le_of_mem_perfectMatchingInstance`: a vertex constraint has at
  most as many variables as the vertex has neighbours.
* `Cslib.Complexity.Graph.card_neighborSet_le`: a vertex has at most as many neighbours as entries
  of the edge list at it, which makes a degree bound checkable.
-/

public section

namespace Cslib.Complexity.Graph

open Cslib.Logic.PL

/-- The perfect-matching instance of `G`: a variable for each position of `G.edgeList`, and an
exactly-one constraint for each distinct declared vertex on the positions of its incident
edges. -/
@[expose] def perfectMatchingInstance (G : Graph) : CSP Unit ℕ :=
  G.distinctVertices.map fun v =>
    ((), (List.range G.edgeList.length).filter fun i => incident (G.edgeList.getD i (0, 0)) v)

variable {G : Graph}

/-! ### The instance -/

/-- The variables of the perfect-matching instance are the positions of the edge list. -/
theorem mem_vars_perfectMatchingInstance {x : ℕ} :
    x ∈ G.perfectMatchingInstance.vars ↔ x < G.edgeList.length := by
  simp only [perfectMatchingInstance, CSP.vars, List.flatMap_map, List.mem_flatMap,
    List.mem_filter, List.mem_range, mem_distinctVertices]
  refine ⟨fun ⟨_, _, hx, _⟩ => hx, fun hx => ⟨_, (of_mem_edgeList (getD_edgeList_mem hx)).2.2.1,
    hx, by simp [incident]⟩⟩

/-- The exactly-one conditions of the perfect-matching instance on a set `S` of positions: every
declared vertex is an end of exactly one edge at a position in `S`. -/
private theorem forall_mem_perfectMatchingInstance_iff {S : Finset ℕ} :
    (∀ c ∈ G.perfectMatchingInstance, (c.2.filter fun v => v ∈ S).length = 1) ↔
      ∀ v ∈ G.1, ∃! i, i < G.edgeList.length ∧ incident (G.edgeList.getD i (0, 0)) v = true ∧
        i ∈ S := by
  simp only [perfectMatchingInstance, List.forall_mem_map, mem_distinctVertices,
    List.filter_filter, List.length_filter_range_eq_one_iff, Bool.and_eq_true, decide_eq_true_eq]
  exact forall₂_congr fun v _ => existsUnique_congr fun i => by tauto

/-- **The exactly-one partition function of the perfect-matching instance is the number of
perfect matchings** of `G.induced`. -/
theorem partitionFunction_perfectMatchingInstance (G : Graph) :
    G.perfectMatchingInstance.partitionFunction CSP.exactlyOneWeight =
      Nat.card {M : G.induced.Subgraph // M.IsPerfectMatching} := by
  classical
  rw [CSP.partitionFunction_exactlyOne,
    Finset.filter_congr fun S _ => forall_mem_perfectMatchingInstance_iff, ← Nat.card_eq_finsetCard]
  have hsub : ∀ {S : Finset ℕ}, S ⊆ G.perfectMatchingInstance.vars.toFinset ↔
      ∀ i ∈ S, i < G.edgeList.length := fun {S} => by
    simp only [Finset.subset_iff, List.mem_toFinset, mem_vars_perfectMatchingInstance]
  symm
  refine Nat.card_congr
    { toFun := fun M => ⟨positions M.1, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr
        (hsub.mpr fun i hi => (mem_positions.mp hi).1),
        (fun v hv => cover_positions M.2.1 v hv (M.2.2 _))⟩⟩
      invFun := fun S => ⟨ofPositions G S.1, isPerfectMatching_ofPositions
        (hsub.mp (Finset.mem_powerset.mp (Finset.mem_filter.mp S.2).1))
        (Finset.mem_filter.mp S.2).2⟩
      left_inv := fun M => ?_
      right_inv := fun S => ?_ }
  · -- the subgraph of the positions of a perfect matching is the matching
    obtain ⟨M, hM⟩ := M
    refine Subtype.ext (SimpleGraph.Subgraph.ext ?_ ?_)
    · exact (Set.eq_univ_of_forall hM.2).symm
    · funext u w
      refine propext ⟨fun ⟨_, i, hi, he⟩ => ?_, fun h => ⟨M.adj_sub h, ?_⟩⟩
      · obtain ⟨-, hu, hw, hadj⟩ := mem_positions.mp hi
        rcases he with he | he <;> simp only [he] at hu hw hadj
        · exact hadj
        · exact hadj.symm
      · obtain ⟨i, hi, hie⟩ := exists_getD_edgeList_of_adj (M.adj_sub h)
        refine ⟨i, mem_positions.mpr ⟨hi, ?_⟩, hie⟩
        rcases hie with hie | hie
        · rw [hie]
          exact ⟨u.2, w.2, h⟩
        · rw [hie]
          exact ⟨w.2, u.2, h.symm⟩
  · -- the positions of the subgraph spanned by a set of positions are that set
    obtain ⟨S, hS⟩ := S
    have hS' := hsub.mp (Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1)
    refine Subtype.ext (Finset.ext fun i => ⟨fun hi => ?_, fun hi => ?_⟩)
    · obtain ⟨hi, hu, hw, ⟨-, j, hj, he⟩⟩ := mem_positions.mp hi
      have := eq_of_getD_edgeList (hS' j hj) hi (by
        rcases he with he | he
        · exact Or.inl (by rw [he])
        · exact Or.inr (by rw [he]; rfl))
      exact this ▸ hj
    · have hlt := hS' i hi
      obtain ⟨hG, hne, h1, h2⟩ := of_mem_edgeList (getD_edgeList_mem hlt)
      refine mem_positions.mpr ⟨hlt, h1, h2, ?_, i, hi, Or.inl rfl⟩
      rw [induced_adj, toSimpleGraph_adj]
      exact ⟨hne, Or.inl hG⟩

/-! ### Occurrences and arities -/

/-- The constraints of the perfect-matching instance: one for each distinct declared vertex. -/
theorem length_perfectMatchingInstance (G : Graph) :
    G.perfectMatchingInstance.length = G.1.toFinset.card := by
  rw [perfectMatchingInstance, List.length_map, length_distinctVertices]

/-- **Every variable occurs at most twice**: in the constraints of the two ends of its edge. -/
theorem count_vars_perfectMatchingInstance (G : Graph) (x : ℕ) :
    G.perfectMatchingInstance.vars.count x ≤ 2 := by
  classical
  set a := (G.edgeList.getD x (0, 0)).1
  set b := (G.edgeList.getD x (0, 0)).2
  let scope (v : ℕ) : List ℕ :=
    (List.range G.edgeList.length).filter fun i => incident (G.edgeList.getD i (0, 0)) v
  have hle : ∀ v, (scope v).count x ≤ (if v = a then 1 else 0) + (if v = b then 1 else 0) := by
    intro v
    by_cases hx : x ∈ scope v
    · have h1 : (scope v).count x ≤ 1 :=
        List.nodup_iff_count_le_one.mp (List.nodup_range.filter _) x
      have hinc := (List.mem_filter.mp hx).2
      simp only [incident, Bool.or_eq_true, decide_eq_true_eq] at hinc
      rcases hinc with h | h <;> subst h <;> split_ifs <;> omega
    · rw [List.count_eq_zero_of_not_mem hx]
      exact Nat.zero_le _
  have hvars : G.perfectMatchingInstance.vars = G.distinctVertices.flatMap scope := by
    simp only [perfectMatchingInstance, CSP.vars, List.flatMap_map, scope]
  rw [hvars, List.count_flatMap, ← List.sum_toFinset _ G.nodup_distinctVertices]
  calc ∑ v ∈ G.distinctVertices.toFinset, (scope v).count x
      ≤ ∑ v ∈ G.distinctVertices.toFinset, ((if v = a then 1 else 0) + (if v = b then 1 else 0)) :=
        Finset.sum_le_sum fun v _ => hle v
    _ ≤ 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
        split_ifs <;> omega

/-- **A vertex constraint has at most as many variables as the vertex has neighbours.** -/
theorem length_le_of_mem_perfectMatchingInstance {d : ℕ}
    (hdeg : ∀ v, Nat.card (G.induced.neighborSet v) ≤ d) {c : Constraint Unit ℕ}
    (hc : c ∈ G.perfectMatchingInstance) : c.2.length ≤ d := by
  classical
  simp only [perfectMatchingInstance, List.mem_map, mem_distinctVertices] at hc
  obtain ⟨v, hv, rfl⟩ := hc
  -- send the position of an edge at `v` to the other end of the edge
  let other (i : ℕ) : ℕ :=
    if (G.edgeList.getD i (0, 0)).1 = v then (G.edgeList.getD i (0, 0)).2
    else (G.edgeList.getD i (0, 0)).1
  have hlen : ((List.range G.edgeList.length).filter fun i =>
      incident (G.edgeList.getD i (0, 0)) v).length =
      ((Finset.range G.edgeList.length).filter fun i =>
        incident (G.edgeList.getD i (0, 0)) v = true).card := rfl
  have hnbr : ((G.induced.neighborSet ⟨v, hv⟩).toFinset.map (Function.Embedding.subtype _)).card ≤
      d := by
    rw [Finset.card_map, Set.toFinset_card, ← Nat.card_eq_fintype_card]
    exact hdeg _
  refine hlen.trans_le ((Finset.card_le_card_of_injOn other (fun i hi => ?_) ?_).trans hnbr)
  · obtain ⟨hi, hinc⟩ := Finset.mem_filter.mp hi
    rw [Finset.mem_range] at hi
    obtain ⟨hG, hne, h1, h2⟩ := of_mem_edgeList (getD_edgeList_mem hi)
    simp only [incident, Bool.or_eq_true, decide_eq_true_eq] at hinc
    have hother : ∃ h : other i ∈ G.1, G.induced.Adj ⟨v, hv⟩ ⟨other i, h⟩ := by
      simp only [other]
      split_ifs with h
      · refine ⟨h2, ?_⟩
        rw [induced_adj, toSimpleGraph_adj]
        subst h
        exact ⟨hne, Or.inl hG⟩
      · refine ⟨h1, ?_⟩
        rw [induced_adj, toSimpleGraph_adj]
        have h' := hinc.resolve_left h
        subst h'
        exact ⟨hne.symm, Or.inr hG⟩
    obtain ⟨hmem, hadj⟩ := hother
    exact Finset.mem_map.mpr ⟨⟨other i, hmem⟩, Set.mem_toFinset.mpr hadj, rfl⟩
  · intro i hi j hj hij
    obtain ⟨hi, hinci⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hi)
    obtain ⟨hj, hincj⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hj)
    rw [Finset.mem_range] at hi hj
    refine eq_of_getD_edgeList hi hj ?_
    simp only [incident, Bool.or_eq_true, decide_eq_true_eq] at hinci hincj
    simp only [other] at hij
    generalize G.edgeList.getD i (0, 0) = ei at *
    generalize G.edgeList.getD j (0, 0) = ej at *
    obtain ⟨p, q⟩ := ei
    obtain ⟨p', q'⟩ := ej
    simp only [Prod.mk.injEq, Prod.swap_prod_mk] at hinci hincj hij ⊢
    split_ifs at hij <;> omega

/-- **A vertex has at most as many neighbours as edge-list entries at it**, so a degree bound can
be checked on the edge list. -/
theorem card_neighborSet_le (v : {v // v ∈ G.1}) :
    Nat.card (G.induced.neighborSet v) ≤ (G.edgeList.filter fun e => incident e v).length := by
  classical
  have hnd : (G.edgeList.filter fun e => incident e v).Nodup :=
    ((pairwise_edgeList G).imp fun h => h.1.symm).filter _
  -- send a neighbour `w` to the entry of the edge `vw`
  have hedge : ∀ w : G.induced.neighborSet v, ∃ e ∈ G.edgeList.filter fun e => incident e v,
      e = (v.1, w.1.1) ∨ e = (w.1.1, v.1) := fun w => by
    rcases exists_mem_edgeList w.2 with h | h
    · exact ⟨_, List.mem_filter.mpr ⟨h, by simp [incident]⟩, Or.inl rfl⟩
    · exact ⟨_, List.mem_filter.mpr ⟨h, by simp [incident]⟩, Or.inr rfl⟩
  let f (w : G.induced.neighborSet v) : (G.edgeList.filter fun e => incident e v).toFinset :=
    ⟨(hedge w).choose, List.mem_toFinset.mpr (hedge w).choose_spec.1⟩
  have hf : Function.Injective f := fun w w' h => by
    have h' := congrArg Subtype.val h
    have hw := (hedge w).choose_spec.2
    have hw' := (hedge w').choose_spec.2
    simp only [f] at h'
    rw [h'] at hw
    have hne : (w.1 : ℕ) ≠ v.1 := fun h => G.induced.ne_of_adj w.2 (Subtype.ext h).symm
    have hne' : (w'.1 : ℕ) ≠ v.1 := fun h => G.induced.ne_of_adj w'.2 (Subtype.ext h).symm
    refine Subtype.ext (Subtype.ext ?_)
    rcases hw with hw | hw <;> rcases hw' with hw' | hw' <;> rw [hw] at hw' <;>
      simp only [Prod.mk.injEq] at hw' <;> omega
  calc Nat.card (G.induced.neighborSet v)
      ≤ Nat.card (G.edgeList.filter fun e => incident e v).toFinset :=
        Nat.card_le_card_of_injective f hf
    _ = _ := by rw [Nat.card_eq_finsetCard, List.toFinset_card_of_nodup hnd]

end Cslib.Complexity.Graph
