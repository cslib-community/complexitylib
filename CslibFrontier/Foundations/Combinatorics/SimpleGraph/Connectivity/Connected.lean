/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Combinatorics/SimpleGraph/Connectivity/Connected.lean`)

public import CslibFrontier.Init
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Empty cuts of disconnected graphs

A graph on a nonempty finite vertex set that is not connected has a vertex set `S` with
`1 ≤ |S|`, `2 |S| ≤ |V|` and no edge between `S` and its complement
(`SimpleGraph.exists_forall_not_adj_of_not_connected`): take the reachability class of a vertex
or its complement, whichever is smaller. This is the combinatorial step of the union bound over
cuts for the connectivity of random graphs.
-/

public section

open Finset
open scoped Finset

namespace SimpleGraph

variable {V : Type*}

/-- A graph on a nonempty finite vertex set that is not connected has a nonempty vertex set `S`
with at most half of the vertices and no edge between `S` and its complement. -/
theorem exists_forall_not_adj_of_not_connected [Fintype V] [Nonempty V]
    {G : SimpleGraph V} (hG : ¬G.Connected) :
    ∃ S : Finset V, 1 ≤ #S ∧ 2 * #S ≤ Fintype.card V ∧ ∀ u ∈ S, ∀ v ∉ S, ¬G.Adj u v := by
  classical
  rw [connected_iff] at hG
  simp only [‹Nonempty V›, and_true, Preconnected, not_forall] at hG
  obtain ⟨u, v, huv⟩ := hG
  set C : Finset V := {w | G.Reachable u w} with hC
  have hclosed : ∀ a b, G.Adj a b → (a ∈ C ↔ b ∈ C) := fun a b hab => by
    simp only [hC, mem_filter, mem_univ, true_and]
    exact ⟨fun h => h.trans hab.reachable, fun h => h.trans hab.symm.reachable⟩
  have huC : u ∈ C := by simp [hC]
  have hvC : v ∉ C := by simpa [hC] using huv
  have hsum : #C + #Cᶜ = Fintype.card V := card_add_card_compl C
  by_cases h : 2 * #C ≤ Fintype.card V
  · refine ⟨C, card_pos.2 ⟨u, huC⟩, h, fun a ha b hb hab => hb ((hclosed a b hab).1 ha)⟩
  · refine ⟨Cᶜ, card_pos.2 ⟨v, mem_compl.2 hvC⟩, by omega, fun a ha b hb hab => ?_⟩
    rw [mem_compl] at ha hb
    rw [not_not] at hb
    exact ha ((hclosed a b hab).2 hb)

/-- Every disconnected finite nonempty graph without isolated vertices contains a connected induced
subgraph on a vertex subset `S` with `2 ≤ #S ≤ |V| / 2` and no edges leaving `S`. -/
theorem exists_connected_induce_forall_not_adj_of_not_connected {V : Type*} [Fintype V]
    [Nonempty V] {G : SimpleGraph V} (hnc : ¬G.Connected)
    (hni : ∀ v, ¬G.IsIsolated v) :
    ∃ S : Finset V, 2 ≤ #S ∧ 2 * #S ≤ Fintype.card V ∧ (G.induce (S : Set V)).Connected ∧
      ∀ u ∈ S, ∀ v ∉ S, ¬G.Adj u v := by
  classical
  let K : V → Finset V := fun u => Finset.univ.filter fun w => G.Reachable u w
  have hK_mem : ∀ u w : V, w ∈ K u ↔ G.Reachable u w := fun u w => by
    simp [K]
  obtain ⟨u₀, _, hu₀min⟩ :=
    Finset.exists_min_image Finset.univ (fun u => #(K u)) Finset.univ_nonempty
  have hnotuniv : ∃ v₀ : V, v₀ ∉ K u₀ := by
    by_contra! hall
    apply hnc
    refine ⟨fun a b => ?_⟩
    exact ((hK_mem u₀ a).mp (hall a)).symm.trans ((hK_mem u₀ b).mp (hall b))
  obtain ⟨v₀, hv₀⟩ := hnotuniv
  have hdisj : Disjoint (K u₀) (K v₀) := by
    rw [Finset.disjoint_left]
    intro w hwu hwv
    exact hv₀ ((hK_mem u₀ v₀).mpr (((hK_mem u₀ w).mp hwu).trans ((hK_mem v₀ w).mp hwv).symm))
  have hsum_card : #(K u₀) + #(K v₀) ≤ Fintype.card V := by
    rw [← Finset.card_union_of_disjoint hdisj]
    exact Finset.card_le_univ _
  have hle_half : 2 * #(K u₀) ≤ Fintype.card V := by
    have hmin := hu₀min v₀ (Finset.mem_univ v₀)
    omega
  have hcard_ge_two : 2 ≤ #(K u₀) := by
    by_contra! hlt
    have hu₀mem : u₀ ∈ K u₀ := (hK_mem u₀ u₀).mpr Reachable.rfl
    have hK_eq : K u₀ = {u₀} := by
      rw [Finset.eq_singleton_iff_unique_mem]
      refine ⟨hu₀mem, fun w hw => ?_⟩
      by_contra hne
      have hsub : {u₀, w} ⊆ K u₀ := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption
      have h2 := Finset.card_le_card hsub
      rw [Finset.card_pair (Ne.symm hne)] at h2
      omega
    have hisol : G.IsIsolated u₀ := by
      intro w hadj
      have hw : w ∈ K u₀ := (hK_mem u₀ w).mpr hadj.reachable
      rw [hK_eq, Finset.mem_singleton] at hw
      exact hadj.ne hw.symm
    exact hni u₀ hisol
  have hind_conn : (G.induce (K u₀ : Set V)).Connected := by
    have hu₀S : u₀ ∈ (K u₀ : Set V) := (hK_mem u₀ u₀).mpr Reachable.rfl
    have hwalk : ∀ z u (q : G.Walk z u), u = u₀ → ∀ hz : z ∈ (K u₀ : Set V),
        (G.induce (K u₀ : Set V)).Reachable ⟨z, hz⟩ ⟨u₀, hu₀S⟩ := by
      intro z u q
      induction q with
      | nil =>
        intro hzu hz
        subst hzu
        exact Reachable.rfl
      | @cons a b c hadj p ih =>
        intro hcu ha
        have hp : G.Reachable b u₀ := hcu ▸ p.reachable
        have hb : b ∈ (K u₀ : Set V) := (hK_mem u₀ b).mpr hp.symm
        have hind_adj : (G.induce (K u₀ : Set V)).Adj ⟨a, ha⟩ ⟨b, hb⟩ := hadj
        exact Reachable.trans hind_adj.reachable (ih hcu hb)
    exact @Connected.mk _ (G.induce (K u₀ : Set V))
      (fun a b => (hwalk a.1 u₀ (Classical.choice ((hK_mem u₀ a.1).mp a.2).symm) rfl a.2).trans
        (hwalk b.1 u₀ (Classical.choice ((hK_mem u₀ b.1).mp b.2).symm) rfl b.2).symm)
      ⟨⟨u₀, hu₀S⟩⟩
  refine ⟨K u₀, hcard_ge_two, hle_half, hind_conn, fun x hx y hy hadj => ?_⟩
  exact hy ((hK_mem u₀ y).mpr (((hK_mem u₀ x).mp hx).trans hadj.reachable))

private theorem exists_adj_leaving_of_walk {V : Type*} {G : SimpleGraph V} {S : Finset V}
    {a b : V} (ha : a ∈ S) (hb : b ∉ S) (p : G.Walk a b) :
    ∃ x ∈ S, ∃ y ∉ S, G.Adj x y := by
  induction p with
  | nil => exact False.elim (hb ha)
  | @cons u v w hadj q ih =>
    by_cases hv : v ∈ S
    · exact ih hv hb
    · exact ⟨u, ha, v, hv, hadj⟩

private theorem exists_tree_edges_aux {V : Type*} [Fintype V]
    {G : SimpleGraph V} (hc : G.Connected) :
    ∀ m : ℕ, ∀ S : Finset V, ∀ t : Finset (Sym2 V),
      S.Nonempty → #t = #S - 1 → (∀ e ∈ t, e ∈ G.edgeSet ∧ ∀ u ∈ e, u ∈ S) →
      Fintype.card V - #S = m →
      ∃ t' : Finset (Sym2 V), #t' = Fintype.card V - 1 ∧ ∀ e ∈ t', e ∈ G.edgeSet := by
  classical
  intro m
  induction m with
  | zero =>
    intro S t _ ht hinv hm
    have hcard : #S = Fintype.card V := by
      have hle := Finset.card_le_univ S
      omega
    exact ⟨t, by omega, fun e he => (hinv e he).1⟩
  | succ m ih =>
    intro S t hSne ht hinv hm
    have hSpos : 0 < #S := Finset.card_pos.mpr hSne
    have hne_univ : S ≠ Finset.univ := by
      intro h
      rw [h, Finset.card_univ] at hm
      omega
    obtain ⟨w, hw⟩ : ∃ w : V, w ∉ S := by
      by_contra! hall
      apply hne_univ
      exact Finset.eq_univ_iff_forall.mpr hall
    obtain ⟨u, hu⟩ := hSne
    obtain ⟨p⟩ := hc.preconnected u w
    obtain ⟨x, hx, y, hy, hadj⟩ := exists_adj_leaving_of_walk hu hw p
    let e : Sym2 V := s(x, y)
    have he_not : e ∉ t := by
      intro he
      exact hy ((hinv e he).2 y (by simp [e]))
    have ht' : #(insert e t) = #(insert y S) - 1 := by
      rw [Finset.card_insert_of_notMem he_not, Finset.card_insert_of_notMem hy]
      omega
    have hinv' : ∀ e' ∈ insert e t, e' ∈ G.edgeSet ∧ ∀ z ∈ e', z ∈ insert y S := by
      intro e' he'
      rcases Finset.mem_insert.mp he' with rfl | he'
      · refine ⟨hadj, fun z hz => ?_⟩
        simp only [e, Sym2.mem_iff] at hz
        rcases hz with hz | hz
        · rw [hz]
          exact Finset.mem_insert_of_mem hx
        · rw [hz]
          exact Finset.mem_insert_self y S
      · refine ⟨(hinv e' he').1, fun z hz => Finset.mem_insert_of_mem ((hinv e' he').2 z hz)⟩
    have hm' : Fintype.card V - #(insert y S) = m := by
      rw [Finset.card_insert_of_notMem hy]
      omega
    exact ih (insert y S) (insert e t) ⟨y, Finset.mem_insert_self y S⟩ ht' hinv' hm'

/-- Every connected finite nonempty graph contains a spanning tree edge subset of cardinality
`|V| - 1`. All elements of this subset are non-diagonal edges of `G`. -/
theorem exists_card_sub_one_subset_edgeSet_of_connected {V : Type*} [Fintype V] [Nonempty V]
    {G : SimpleGraph V} (hc : G.Connected) :
    ∃ t : Finset (Sym2 V), #t = Fintype.card V - 1 ∧ ∀ e ∈ t, e ∈ G.edgeSet ∧ ¬e.IsDiag := by
  classical
  let v₀ : V := Classical.arbitrary V
  obtain ⟨t, ht, hedge⟩ := exists_tree_edges_aux hc (Fintype.card V - 1) {v₀} ∅
    ⟨v₀, Finset.mem_singleton_self v₀⟩ (by simp) (fun _ h => by simp at h) (by simp)
  refine ⟨t, ht, fun e he => ⟨hedge e he, ?_⟩⟩
  induction e using Sym2.ind with
  | _ a b =>
    have hab : G.Adj a b := hedge _ he
    exact hab.ne

end SimpleGraph
