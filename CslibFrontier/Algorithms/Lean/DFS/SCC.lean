/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.DFS.TopologicalSort
import CslibFrontier.Algorithms.Lean.TimeM.Loops

/-!
# Strongly connected components

Kosaraju's linear-time algorithm for the strongly connected components of a directed graph given by
adjacency lists `adj : V → List V`, together with their condensation topological order, following
[Cormen et al.][CLRS2009] (see also [Tarjan][Tarjan1972]).

From a vertex list `vs` covering `V`, `Cslib.Algorithms.Lean.DFS.sccs adj vs`:
1. computes the finishing order `ord = topologicalSort adj vs` of depth-first search on `adj`;
2. builds the transpose adjacency lists `transposeAdj adj vs` by scanning `vs` and `adj u`;
3. traverses `ord` in the transpose graph (`peelSCCs`), emitting each newly reached tree as one
   strongly connected component.

Because the component finishing lemma (`dfs_scc_finished_order`) places at least one vertex of
every upstream component before every vertex of a downstream component in `ord`, each root peeled
in `transposeAdj adj vs` sees no unvisited upstream vertices and visits its exact strongly
connected component. Moreover, emitted components appear in forward topological order of the
condensation DAG: every edge `u → v` goes from a component of index `i` to a component of index
`j` with `i ≤ j`.

## Main definitions

* `Cslib.Algorithms.Lean.DFS.IsSCCCondensation`: specification of a duplicate-free partition of `V`
  into nonempty `StronglyConnected` classes ordered topologically.
* `Cslib.Algorithms.Lean.DFS.transposeAdj`, `Cslib.Algorithms.Lean.DFS.transposeAdjM`: transpose
  adjacency lists, pure and in `TimeM`.
* `Cslib.Algorithms.Lean.DFS.sccs`, `Cslib.Algorithms.Lean.DFS.sccsM`: Kosaraju's algorithm, pure
  and in `TimeM`.
* `Cslib.Algorithms.Lean.DFS.indexComponents`, `Cslib.Algorithms.Lean.DFS.indexComponentsM`: map
  each vertex to its component's topological index in `O(|V|)` steps.

## Main results

* `Cslib.Algorithms.Lean.DFS.isSCCCondensation_sccs`: when `vs` lists every vertex, `sccs adj vs`
  satisfies `IsSCCCondensation adj`.
* `Cslib.Algorithms.Lean.DFS.time_sccsM`, `Cslib.Algorithms.Lean.DFS.time_sccsM_of_nodup`: exact
  linear `TimeM` cost (`3 * (|vs| + ∑ v, |adj v|)` when `vs` is duplicate-free).
* `Cslib.Algorithms.Lean.DFS.IsSCCCondensation.indexComponents_eq_iff`,
  `Cslib.Algorithms.Lean.DFS.IsSCCCondensation.indexComponents_le_of_edge`: component-index
  equivalence and condensation monotonicity.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009]
* [R. E. Tarjan, *Depth-first search and linear graph algorithms*][Tarjan1972]
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.DFS

open scoped List
open TimeM

variable {V : Type*}

/-! ### Condensation specification -/

/-- A topological decomposition of `(V, adj)` into strongly connected components: nonempty lists
partitioning `V` without duplicates, each an equivalence class of `StronglyConnected adj`, ordered
so every edge `u → v` has `u`'s component index at most `v`'s. -/
structure IsSCCCondensation (adj : V → List V) (comps : List (List V)) : Prop where
  /-- Every component is nonempty. -/
  ne_nil : ∀ c ∈ comps, c ≠ []
  /-- Across all components, no vertex appears twice. -/
  nodup_flatten : comps.flatten.Nodup
  /-- Every vertex appears in some component. -/
  mem_flatten : ∀ v, v ∈ comps.flatten
  /-- Two vertices share a component if and only if they are mutually reachable. -/
  same_comp_iff : ∀ u v, (∃ c ∈ comps, u ∈ c ∧ v ∈ c) ↔ StronglyConnected adj u v
  /-- Every edge `u → v` goes from component `i` to component `j` with `i ≤ j`. -/
  condensation_le : ∀ {i j : ℕ} (hi : i < comps.length) (hj : j < comps.length) {u v : V},
    u ∈ comps[i] → v ∈ comps[j] → Edge adj u v → i ≤ j

/-! ### Transpose adjacency lists -/

/-- Reverse every adjacency-list arc emanating from `vs`. -/
def transposeAdj [DecidableEq V] (adj : V → List V) (vs : List V) : V → List V :=
  vs.foldl (fun rev u => (adj u).foldl (fun rev v => Function.update rev v (u :: rev v)) rev)
    (fun _ => [])

/-- `transposeAdj` in `TimeM`, charging one unit per vertex of `vs` and one per arc scanned. -/
def transposeAdjM [DecidableEq V] (adj : V → List V) (vs : List V) : TimeM ℕ (V → List V) :=
  vs.foldlM
    (fun rev u => do
      ✓
      (adj u).foldlM (fun rev v => do ✓ return Function.update rev v (u :: rev v)) rev)
    (fun _ => [])

section Transpose

variable [DecidableEq V] {adj : V → List V}

private theorem foldl_transpose_mem (u : V) :
    ∀ (l : List V) (rev : V → List V) (w x : V),
      x ∈ (l.foldl (fun rev v => Function.update rev v (u :: rev v)) rev) w ↔
        x ∈ rev w ∨ (x = u ∧ w ∈ l)
  | [], rev, w, x => by simp
  | v :: l, rev, w, x => by
    rw [List.foldl_cons, foldl_transpose_mem]
    by_cases hwv : w = v
    · subst hwv
      simp only [Function.update_self, List.mem_cons]
      tauto
    · simp only [Function.update_of_ne hwv, List.mem_cons]
      tauto

private theorem foldl_vs_transpose_mem :
    ∀ (vs : List V) (rev : V → List V) (w x : V),
      x ∈ (vs.foldl
          (fun rev u => (adj u).foldl (fun rev v => Function.update rev v (u :: rev v)) rev)
          rev) w ↔
        x ∈ rev w ∨ (x ∈ vs ∧ w ∈ adj x)
  | [], rev, w, x => by simp
  | u :: vs, rev, w, x => by
    rw [List.foldl_cons, foldl_vs_transpose_mem, foldl_transpose_mem]
    simp only [List.mem_cons]
    constructor
    · rintro ((hx | ⟨rfl, hw⟩) | ⟨hx, hw⟩)
      · exact .inl hx
      · exact .inr ⟨.inl rfl, hw⟩
      · exact .inr ⟨.inr hx, hw⟩
    · rintro (hx | ⟨rfl | hx, hw⟩)
      · exact .inl (.inl hx)
      · exact .inl (.inr ⟨rfl, hw⟩)
      · exact .inr ⟨hx, hw⟩

theorem mem_transposeAdj {vs : List V} {w x : V} :
    x ∈ transposeAdj adj vs w ↔ x ∈ vs ∧ w ∈ adj x := by
  simpa [transposeAdj] using foldl_vs_transpose_mem (adj := adj) vs (fun _ => []) w x

theorem edge_transposeAdj_iff {vs : List V} (hvs : ∀ v, v ∈ vs) {u v : V} :
    Edge (transposeAdj adj vs) u v ↔ Edge adj v u := by
  simp [Edge, mem_transposeAdj, hvs v]

theorem reflTransGen_edge_transposeAdj_iff {vs : List V} (hvs : ∀ v, v ∈ vs) {u v : V} :
    Relation.ReflTransGen (Edge (transposeAdj adj vs)) u v ↔
      Relation.ReflTransGen (Edge adj) v u := by
  have hrel : Edge (transposeAdj adj vs) = Function.swap (Edge adj) :=
    funext fun a => funext fun b => propext (edge_transposeAdj_iff hvs)
  rw [hrel, Relation.reflTransGen_swap]

theorem ret_transposeAdjM (adj : V → List V) (vs : List V) :
    (transposeAdjM adj vs).ret = transposeAdj adj vs := by
  simp only [transposeAdjM, transposeAdj, TimeM.ret_foldlM, TimeM.ret_bind, TimeM.ret_pure]

theorem time_transposeAdjM (adj : V → List V) (vs : List V) :
    (transposeAdjM adj vs).time = vs.length + outDegreeSum adj vs := by
  rw [transposeAdjM, TimeM.time_foldlM_eq_sum _ (fun u => 1 + (adj u).length)]
  · rw [List.sum_map_add]
    simp [outDegreeSum]
  · intro rev u
    simp only [TimeM.time_bind, TimeM.time_tick]
    rw [TimeM.time_foldlM_of_time_eq _ _ _ (c := 1) (fun _ _ => rfl)]
    omega

omit [DecidableEq V] in
/-- Consing onto one adjacency-list entry increases the total adjacency-list length by `1`. -/
theorem sum_length_update_cons {α β : Type*} [DecidableEq α] [Fintype α] (f : α → List β)
    (u : α) (v : β) :
    (∑ w, (Function.update f u (v :: f u) w).length) = (∑ w, (f w).length) + 1 := by
  change (∑ w, (List.length ∘ Function.update f u (v :: f u)) w) = _
  rw [Function.comp_update List.length f u (v :: f u)]
  change (∑ w, Function.update (fun w => (f w).length) u (v :: f u).length w) = _
  rw [Finset.sum_update_of_mem (Finset.mem_univ u)]
  rw [← Finset.add_sum_erase _ (fun w => (f w).length) (Finset.mem_univ u)]
  rw [List.length_cons]
  rw [Finset.erase_eq]
  omega
private theorem sum_length_foldl_update [Fintype V] (u : V) :
    ∀ (l : List V) (rev : V → List V),
      (∑ w, ((l.foldl (fun rev v => Function.update rev v (u :: rev v)) rev) w).length) =
        (∑ w, (rev w).length) + l.length
  | [], rev => by simp
  | v :: l, rev => by
    rw [List.foldl_cons, sum_length_foldl_update u l, List.length_cons, sum_length_update_cons]
    omega

private theorem sum_length_foldl_vs [Fintype V] :
    ∀ (vs : List V) (rev : V → List V),
      (∑ w, ((vs.foldl
          (fun rev u => (adj u).foldl (fun rev v => Function.update rev v (u :: rev v)) rev)
          rev) w).length) =
        (∑ w, (rev w).length) + outDegreeSum adj vs
  | [], rev => by simp [outDegreeSum]
  | u :: vs, rev => by
    rw [List.foldl_cons, sum_length_foldl_vs, sum_length_foldl_update]
    simp only [outDegreeSum, List.map_cons, List.sum_cons]
    omega

theorem sum_length_transposeAdj [Fintype V] (adj : V → List V) (vs : List V) :
    (∑ w, (transposeAdj adj vs w).length) = outDegreeSum adj vs := by
  simpa [transposeAdj] using sum_length_foldl_vs (adj := adj) vs (fun _ => [])

end Transpose

/-! ### Kosaraju's second pass -/

/-- Peel strongly connected components in `revAdj` along finishing order `rs`. -/
def peelSCCs [DecidableEq V] (revAdj : V → List V) (k : ℕ) :
    Finset V → List V → List (List V)
  | _, [] => []
  | vis, r :: rs =>
    let s := visit revAdj k r ⟨vis, []⟩
    if s.finished.isEmpty then peelSCCs revAdj k s.visited rs
    else s.finished :: peelSCCs revAdj k s.visited rs

/-- `peelSCCs` in `TimeM`. -/
def peelSCCsM [DecidableEq V] (revAdj : V → List V) (k : ℕ) :
    Finset V → List V → TimeM ℕ (List (List V))
  | _, [] => return []
  | vis, r :: rs => do
    let s ← visitM revAdj k r ⟨vis, []⟩
    let rest ← peelSCCsM revAdj k s.visited rs
    if s.finished.isEmpty then return rest
    else return s.finished :: rest

/-- **Kosaraju's algorithm**: compute strongly connected components in condensation topological
order from a vertex list `vs`. -/
def sccs [DecidableEq V] (adj : V → List V) (vs : List V) : List (List V) :=
  peelSCCs (transposeAdj adj vs) vs.length ∅ (topologicalSort adj vs)

/-- Kosaraju's algorithm in `TimeM`. -/
def sccsM [DecidableEq V] (adj : V → List V) (vs : List V) : TimeM ℕ (List (List V)) := do
  let ord ← topologicalSortM adj vs
  let revAdj ← transposeAdjM adj vs
  peelSCCsM revAdj vs.length ∅ ord

section KosarajuProof

variable [DecidableEq V] {adj : V → List V}

omit [DecidableEq V] in
private theorem outDegreeSum_append (g : V → List V) (a b : List V) :
    outDegreeSum g (a ++ b) = outDegreeSum g a + outDegreeSum g b := by
  simp [outDegreeSum, List.map_append, List.sum_append]

private theorem peelSCCsM_spec (revAdj : V → List V) (k : ℕ) :
    ∀ (vis : Finset V) (rs : List V),
      (peelSCCsM revAdj k vis rs).ret = peelSCCs revAdj k vis rs ∧
      (peelSCCsM revAdj k vis rs).time =
        rs.length + outDegreeSum revAdj (peelSCCs revAdj k vis rs).flatten
  | vis, [] => by simp [peelSCCsM, peelSCCs, outDegreeSum]
  | vis, r :: rs => by
    have hv_ret : (visitM revAdj k r ⟨vis, []⟩).ret = visit revAdj k r ⟨vis, []⟩ :=
      ret_visitM k r ⟨vis, []⟩
    have hv_time : (visitM revAdj k r ⟨vis, []⟩).time =
        1 + outDegreeSum revAdj (visit revAdj k r ⟨vis, []⟩).finished := by
      have ht := time_visitM (adj := revAdj) k r ⟨vis, []⟩
      simpa [outDegreeSum] using ht
    obtain ⟨hr_ret, hr_time⟩ :=
      peelSCCsM_spec revAdj k (visit revAdj k r ⟨vis, []⟩).visited rs
    rw [peelSCCsM, peelSCCs]
    simp only [TimeM.ret_bind, TimeM.time_bind, hv_ret, hv_time, hr_ret, hr_time, List.length_cons]
    split_ifs with he
    · have hnil : (visit revAdj k r ⟨vis, []⟩).finished = [] := List.isEmpty_iff.1 he
      simp only [TimeM.ret_pure, TimeM.time_pure, hnil, outDegreeSum, List.map_nil, List.sum_nil,
        true_and]
      omega
    · simp only [TimeM.ret_pure, TimeM.time_pure, List.flatten_cons, outDegreeSum_append, true_and]
      omega

omit [DecidableEq V] in
private theorem reach_of_closed {g : V → List V} {vis : Finset V}
    (hcl : ∀ u ∈ vis, ∀ v ∈ g u, v ∈ vis) {u w : V} (hu : u ∈ vis)
    (h : Relation.ReflTransGen (Edge g) u w) : w ∈ vis := by
  induction h with
  | refl => exact hu
  | tail _ hbc ih => exact hcl _ ih _ hbc

private theorem dfs_visited_of_closed [Fintype V] {g : V → List V} {k : ℕ}
    (hk : Fintype.card V ≤ k) {vis : Finset V} (hcl : ∀ u ∈ vis, ∀ v ∈ g u, v ∈ vis) :
    (dfs g k vis.toList).visited = vis := by
  ext w
  rw [mem_dfs_visited_iff hk]
  simp only [Finset.mem_toList]
  exact ⟨fun ⟨u, hu, huw⟩ => reach_of_closed hcl hu huw, fun hw => ⟨w, hw, .refl⟩⟩

private theorem visit_nil_spec [Fintype V] {g : V → List V} {k : ℕ}
    (hk : Fintype.card V ≤ k) {vis : Finset V} (hcl : ∀ u ∈ vis, ∀ v ∈ g u, v ∈ vis) (r : V) :
    (∀ w, w ∈ (visit g k r ⟨vis, []⟩).visited ↔
        w ∈ vis ∨ Relation.ReflTransGen (Edge g) r w) ∧
      (visit g k r ⟨vis, []⟩).finished.Nodup ∧
      (∀ w, w ∈ (visit g k r ⟨vis, []⟩).finished ↔
        w ∉ vis ∧ Relation.ReflTransGen (Edge g) r w) := by
  have hd_eq : dfs g k vis.toList = ⟨vis, (dfs g k vis.toList).finished⟩ := by
    cases hd : dfs g k vis.toList with
    | mk v f =>
      have hv : v = vis := by simpa [hd] using dfs_visited_of_closed hk hcl
      simp [hv]
  have hsplit :
      dfs g k (vis.toList ++ [r]) =
        ⟨(visit g k r ⟨vis, []⟩).visited,
          (visit g k r ⟨vis, []⟩).finished ++ (dfs g k vis.toList).finished⟩ := by
    dsimp [dfs]
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    change visit g k r (dfs g k vis.toList) =
      ⟨(visit g k r ⟨vis, []⟩).visited,
        (visit g k r ⟨vis, []⟩).finished ++ (dfs g k vis.toList).finished⟩
    rw [hd_eq, visit_eq_of_nil]
  have hvis : ∀ w, w ∈ (visit g k r ⟨vis, []⟩).visited ↔
      w ∈ vis ∨ Relation.ReflTransGen (Edge g) r w := by
    intro w
    have hm := mem_dfs_visited_iff (adj := g) hk (vis.toList ++ [r]) w
    rw [hsplit] at hm
    simp only [List.mem_append, Finset.mem_toList, List.mem_singleton] at hm
    rw [hm]
    exact ⟨fun ⟨u, hu, huw⟩ =>
        hu.elim (fun huv => .inl (reach_of_closed hcl huv huw)) (fun hur => .inr (hur ▸ huw)),
      fun h => h.elim (fun hw => ⟨w, .inl hw, .refl⟩) (fun hrw => ⟨r, .inr rfl, hrw⟩)⟩
  have hfin_prev : ∀ w, w ∈ (dfs g k vis.toList).finished ↔ w ∈ vis := by
    intro w
    rw [mem_dfs_finished_iff hk, ← mem_dfs_visited_iff hk, dfs_visited_of_closed hk hcl]
  have hnd_all :
      ((visit g k r ⟨vis, []⟩).finished ++ (dfs g k vis.toList).finished).Nodup := by
    have hnd := nodup_dfs_finished (adj := g) hk (vis.toList ++ [r])
    rwa [hsplit] at hnd
  refine ⟨hvis, hnd_all.of_append_left, fun w => ?_⟩
  have hdisj := List.disjoint_of_nodup_append hnd_all
  have hm := mem_dfs_finished_iff (adj := g) hk (vis.toList ++ [r]) w
  rw [← mem_dfs_visited_iff hk, hsplit, List.mem_append, hfin_prev, hvis] at hm
  constructor
  · intro hw
    have hnv : w ∉ vis := fun hwv => hdisj hw ((hfin_prev w).2 hwv)
    exact ⟨hnv, (hm.1 (.inl hw)).resolve_left hnv⟩
  · rintro ⟨hnv, hrw⟩
    exact (hm.2 (.inr hrw)).resolve_right hnv

omit [DecidableEq V] in
private theorem not_sublist_two_head {z r : V} {rs : List V} (hr : r ∉ rs) :
    ¬ [z, r] <+ r :: rs := by
  intro hsub
  rcases List.sublist_cons_iff.1 hsub with h | ⟨l, hl, hl_sub⟩
  · exact hr (h.subset (by simp))
  · injection hl with _ hlr
    subst hlr
    exact hr (hl_sub.subset (by simp))

private theorem peelSCCs_spec [Fintype V] {vs : List V} (hvs : ∀ v, v ∈ vs)
    {k : ℕ} (hk : Fintype.card V ≤ k) :
    ∀ (rs : List V) (vis : Finset V),
      rs.Nodup →
      (∀ u ∈ vis, ∀ v ∈ transposeAdj adj vs u, v ∈ vis) →
      (∀ r ∈ rs, ∀ w, Relation.ReflTransGen (Edge adj) w r →
        ¬ Relation.ReflTransGen (Edge adj) r w →
        w ∈ vis ∨ ∃ z ∈ rs, StronglyConnected adj w z ∧ [z, r] <+ rs) →
      let comps := peelSCCs (transposeAdj adj vs) k vis rs
      (∀ c ∈ comps, c ≠ []) ∧
        comps.flatten.Nodup ∧
        (∀ w, w ∈ comps.flatten ↔
          w ∉ vis ∧ ∃ r ∈ rs, Relation.ReflTransGen (Edge adj) w r) ∧
        (∀ c ∈ comps, ∃ r, ∀ w, w ∈ c ↔ StronglyConnected adj r w) ∧
        (∀ {i j : ℕ} (hi : i < comps.length) (hj : j < comps.length) {u v : V},
          u ∈ comps[i] → v ∈ comps[j] → Edge adj u v → i ≤ j)
  | [], vis, _, _, _ => by
    refine ⟨by simp [peelSCCs], by simp [peelSCCs], by simp [peelSCCs], by simp [peelSCCs], ?_⟩
    intro i _ hi
    simp [peelSCCs] at hi
  | r :: rs, vis, hnd, hcl, hord => by
    rw [List.nodup_cons] at hnd
    rcases hnd with ⟨hr_not_rs, hrs_nd⟩
    set rev := transposeAdj adj vs
    obtain ⟨hvis_s, hnd_s, hfin_s⟩ := visit_nil_spec (g := rev) hk hcl r
    set s := visit rev k r ⟨vis, []⟩
    have hvis_adj : ∀ w, w ∈ s.visited ↔ w ∈ vis ∨ Relation.ReflTransGen (Edge adj) w r := by
      intro w
      rw [hvis_s, reflTransGen_edge_transposeAdj_iff hvs]
    have hfin_adj : ∀ w, w ∈ s.finished ↔ w ∉ vis ∧ Relation.ReflTransGen (Edge adj) w r := by
      intro w
      rw [hfin_s, reflTransGen_edge_transposeAdj_iff hvs]
    have hcl' : ∀ u ∈ s.visited, ∀ v ∈ rev u, v ∈ s.visited := by
      intro u hu v huv
      have hvu : Edge adj v u := (edge_transposeAdj_iff hvs).1 huv
      rw [hvis_adj] at hu ⊢
      rcases hu with hu | hur
      · exact .inl (hcl u hu v huv)
      · exact .inr (Relation.ReflTransGen.head hvu hur)
    have hord' : ∀ r' ∈ rs, ∀ w, Relation.ReflTransGen (Edge adj) w r' →
        ¬ Relation.ReflTransGen (Edge adj) r' w →
        w ∈ s.visited ∨ ∃ z ∈ rs, StronglyConnected adj w z ∧ [z, r'] <+ rs := by
      intro r' hr' w hwr' hnr'w
      rcases hord r' (List.mem_cons_of_mem r hr') w hwr' hnr'w with
        hw_vis | ⟨z, hz_mem, hwz, hz_sub⟩
      · exact .inl ((hvis_adj w).2 (.inl hw_vis))
      · rcases List.mem_cons.1 hz_mem with rfl | hz_rs
        · exact .inl ((hvis_adj w).2 (.inr hwz.1))
        · have hzr : z ≠ r := fun h => hr_not_rs (h ▸ hz_rs)
          have hsub_rs : [z, r'] <+ rs := by
            rcases List.sublist_cons_iff.1 hz_sub with h | ⟨l, hl, _⟩
            · exact h
            · injection hl with hrz _
              exact absurd hrz hzr
          exact .inr ⟨z, hz_rs, hwz, hsub_rs⟩
    obtain ⟨ih_ne, ih_nd, ih_mem, ih_scc, ih_cond⟩ := peelSCCs_spec hvs hk rs s.visited hrs_nd
      hcl' hord'
    rw [peelSCCs]
    change (let comps := if s.finished.isEmpty then peelSCCs rev k s.visited rs
      else s.finished :: peelSCCs rev k s.visited rs; _)
    split_ifs with he
    · have hnil : s.finished = [] := List.isEmpty_iff.1 he
      have hall_vis : ∀ w, Relation.ReflTransGen (Edge adj) w r → w ∈ vis := by
        intro w hwr
        by_contra hnv
        have hm : w ∈ s.finished := (hfin_adj w).2 ⟨hnv, hwr⟩
        simp [hnil] at hm
      refine ⟨ih_ne, ih_nd, fun w => ?_, ih_scc, ih_cond⟩
      rw [ih_mem, hvis_adj]
      constructor
      · rintro ⟨hnv, r', hr', hwr'⟩
        exact ⟨fun hv => hnv (.inl hv), r', List.mem_cons_of_mem r hr', hwr'⟩
      · rintro ⟨hnv, r', hr', hwr'⟩
        rcases List.mem_cons.1 hr' with rfl | hr'
        · exact absurd (hall_vis w hwr') hnv
        · exact ⟨fun h => h.elim hnv (fun hwr => hnv (hall_vis w hwr)), r', hr', hwr'⟩
    · have hne : s.finished ≠ [] := by
        intro hnil
        exact he (List.isEmpty_iff.2 hnil)
      have hr_nvis : r ∉ vis := by
        intro hrv
        obtain ⟨x₀, hx₀⟩ := List.exists_mem_of_ne_nil s.finished hne
        obtain ⟨hnx₀, hx₀r⟩ := (hfin_adj x₀).1 hx₀
        exact hnx₀ (reach_of_closed hcl hrv ((reflTransGen_edge_transposeAdj_iff hvs).2 hx₀r))
      have hs_scc : ∀ w, w ∈ s.finished ↔ StronglyConnected adj r w := by
        intro w
        rw [hfin_adj]
        constructor
        · rintro ⟨hnv, hwr⟩
          refine ⟨?_, hwr⟩
          by_contra hnrw
          rcases hord r List.mem_cons_self w hwr hnrw with hwv | ⟨z, _, _, hsub⟩
          · exact hnv hwv
          · exact not_sublist_two_head hr_not_rs hsub
        · rintro ⟨hrw, hwr⟩
          refine ⟨fun hwv => hr_nvis ?_, hwr⟩
          exact reach_of_closed hcl hwv ((reflTransGen_edge_transposeAdj_iff hvs).2 hrw)
      set rest := peelSCCs rev k s.visited rs
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro c hc
        rcases List.mem_cons.1 hc with rfl | hc
        · exact hne
        · exact ih_ne c hc
      · rw [List.flatten_cons, List.nodup_append]
        refine ⟨hnd_s, ih_nd, fun w hw₁ _ hw₂ hww' => ?_⟩
        subst hww'
        have hw_vis : w ∈ s.visited := (hvis_adj w).2 (.inr ((hfin_adj w).1 hw₁).2)
        exact ((ih_mem w).1 hw₂).1 hw_vis
      · intro w
        rw [List.flatten_cons, List.mem_append, hfin_adj, ih_mem, hvis_adj]
        by_cases hwr : Relation.ReflTransGen (Edge adj) w r
        · simp only [hwr, and_true, or_true, not_true_eq_false, false_and, or_false]
          exact ⟨fun hnv => ⟨hnv, r, List.mem_cons_self, hwr⟩, fun ⟨hnv, _⟩ => hnv⟩
        · simp only [hwr, and_false, or_false, false_or]
          constructor
          · rintro ⟨hnv, r', hr', hwr'⟩
            exact ⟨hnv, r', List.mem_cons_of_mem r hr', hwr'⟩
          · rintro ⟨hnv, r', hr', hwr'⟩
            rcases List.mem_cons.1 hr' with rfl | hr'
            · exact absurd hwr' hwr
            · exact ⟨hnv, r', hr', hwr'⟩
      · intro c hc
        rcases List.mem_cons.1 hc with rfl | hc
        · exact ⟨r, hs_scc⟩
        · exact ih_scc c hc
      · intro i j hi hj u v hu hv huv
        cases i with
        | zero => exact Nat.zero_le j
        | succ i' =>
          cases j with
          | zero =>
            simp only [List.length_cons, List.getElem_cons_succ, List.getElem_cons_zero] at hi hu hv
            have hi' : i' < rest.length := by omega
            have hu_flat : u ∈ rest.flatten :=
              List.mem_flatten.2 ⟨rest[i'], List.getElem_mem hi', hu⟩
            have hu_nvis : u ∉ s.visited := ((ih_mem u).1 hu_flat).1
            have hv_vis : v ∈ s.visited := (hvis_adj v).2 (.inr ((hfin_adj v).1 hv).2)
            exact absurd (hcl' v hv_vis u ((edge_transposeAdj_iff hvs).2 huv)) hu_nvis
          | succ j' =>
            simp only [List.length_cons, List.getElem_cons_succ] at hi hj hu hv
            exact Nat.succ_le_succ (ih_cond (by omega) (by omega) hu hv huv)

/-- **Correctness of Kosaraju's algorithm** [Cormen et al.][CLRS2009]: when `vs` lists every
vertex of `V`, `sccs adj vs` partitions `V` into nonempty strongly connected components in forward
condensation topological order. -/
theorem isSCCCondensation_sccs {vs : List V} (hvs : ∀ v, v ∈ vs) :
    IsSCCCondensation adj (sccs adj vs) := by
  let _ : Fintype V := Fintype.ofList vs hvs
  have hk : Fintype.card V ≤ vs.length := card_le_length hvs
  have hnd : (topologicalSort adj vs).Nodup := nodup_topologicalSort hvs
  have hmem_ord : ∀ v, v ∈ topologicalSort adj vs := mem_topologicalSort hvs
  have hord : ∀ r ∈ topologicalSort adj vs, ∀ w, Relation.ReflTransGen (Edge adj) w r →
      ¬ Relation.ReflTransGen (Edge adj) r w →
      w ∈ (∅ : Finset V) ∨
        ∃ z ∈ topologicalSort adj vs,
          StronglyConnected adj w z ∧ [z, r] <+ topologicalSort adj vs := by
    intro r _ w hwr hnrw
    obtain ⟨z, hwz, hsub⟩ :=
      dfs_scc_finished_order (adj := adj) hk vs (hmem_ord w) hwr hnrw
    exact .inr ⟨z, hmem_ord z, hwz, hsub⟩
  obtain ⟨hne, hnd_flat, hmem_flat, hscc, hcond⟩ :=
    peelSCCs_spec (adj := adj) hvs hk (topologicalSort adj vs) ∅ hnd (by simp) hord
  refine ⟨hne, hnd_flat, ?_, ?_, hcond⟩
  · intro v
    exact (hmem_flat v).2 ⟨Finset.notMem_empty v, v, hmem_ord v, .refl⟩
  · intro u v
    constructor
    · rintro ⟨c, hc, hu, hv⟩
      obtain ⟨r, hr⟩ := hscc c hc
      exact ((hr u).1 hu).symm.trans ((hr v).1 hv)
    · intro huv
      have hu_flat : u ∈ (sccs adj vs).flatten :=
        (hmem_flat u).2 ⟨Finset.notMem_empty u, u, hmem_ord u, .refl⟩
      obtain ⟨c, hc, hu⟩ := List.mem_flatten.1 hu_flat
      obtain ⟨r, hr⟩ := hscc c hc
      exact ⟨c, hc, hu, (hr v).2 (((hr u).1 hu).trans huv)⟩

theorem ret_sccsM (adj : V → List V) (vs : List V) :
    (sccsM adj vs).ret = sccs adj vs := by
  simp only [sccsM, sccs, TimeM.ret_bind, ret_topologicalSortM, ret_transposeAdjM,
    (peelSCCsM_spec _ _ _ _).1]

/-- **Exact `TimeM` cost of `sccsM`** from a covering vertex list `vs`. -/
theorem time_sccsM [Fintype V] {vs : List V} (hvs : ∀ v, v ∈ vs) :
    (sccsM adj vs).time =
      2 * vs.length + Fintype.card V + (∑ v, (adj v).length) + 2 * outDegreeSum adj vs := by
  have hcond := isSCCCondensation_sccs (adj := adj) hvs
  have hord_len : (topologicalSort adj vs).length = Fintype.card V := by
    have hnd := nodup_topologicalSort (adj := adj) hvs
    have hm := mem_topologicalSort (adj := adj) hvs
    rw [← List.toFinset_card_of_nodup hnd]
    congr 1
    ext v
    simp [hm v]
  have hout_rev :
      outDegreeSum (transposeAdj adj vs) (sccs adj vs).flatten = outDegreeSum adj vs := by
    rw [outDegreeSum, ← List.sum_toFinset _ hcond.nodup_flatten]
    have huniv : (sccs adj vs).flatten.toFinset = Finset.univ := by
      ext v
      simp [hcond.mem_flatten v]
    rw [huniv, sum_length_transposeAdj]
  simp only [sccsM, TimeM.time_bind, ret_topologicalSortM, ret_transposeAdjM,
    time_topologicalSortM hvs, time_transposeAdjM, (peelSCCsM_spec _ _ _ _).2]
  change (vs.length + ∑ v, (adj v).length) +
    ((vs.length + outDegreeSum adj vs) +
      ((topologicalSort adj vs).length +
        outDegreeSum (transposeAdj adj vs) (sccs adj vs).flatten)) = _
  rw [hord_len, hout_rev]
  omega

/-- When `vs` lists every vertex without repetition, `sccsM adj vs` costs exactly
`3 * (vs.length + ∑ v, (adj v).length)`. -/
theorem time_sccsM_of_nodup [Fintype V] {vs : List V} (hvs : ∀ v, v ∈ vs) (hnd : vs.Nodup) :
    (sccsM adj vs).time = 3 * (vs.length + ∑ v, (adj v).length) := by
  have huniv : vs.toFinset = Finset.univ := by
    ext v
    simp [hvs v]
  have hcard : Fintype.card V = vs.length := by
    rw [← List.toFinset_card_of_nodup hnd, huniv, Finset.card_univ]
  have hout : outDegreeSum adj vs = ∑ v, (adj v).length := by
    rw [outDegreeSum, ← List.sum_toFinset _ hnd, huniv]
  rw [time_sccsM hvs, hcard, hout]
  omega

end KosarajuProof

/-! ### Component-index table -/

/-- Auxiliary pass assigning each vertex in `c` its component index `idx`. -/
def indexComponentsAux [DecidableEq V] : ℕ → List (List V) → (V → ℕ) → V → ℕ
  | _, [], f => f
  | idx, c :: cs, f =>
    indexComponentsAux (idx + 1) cs (c.foldl (fun f v => Function.update f v idx) f)

/-- Map every vertex to the topological index of its component in `comps`. -/
def indexComponents [DecidableEq V] (comps : List (List V)) : V → ℕ :=
  indexComponentsAux 0 comps (fun _ => 0)

/-- `indexComponentsAux` in `TimeM`, charging one unit per component and one per vertex entry. -/
def indexComponentsAuxM [DecidableEq V] : ℕ → List (List V) → (V → ℕ) → TimeM ℕ (V → ℕ)
  | _, [], f => return f
  | idx, c :: cs, f => do
    ✓
    let f' ← c.foldlM (fun f v => do ✓ return Function.update f v idx) f
    indexComponentsAuxM (idx + 1) cs f'

/-- `indexComponents` in `TimeM`. -/
def indexComponentsM [DecidableEq V] (comps : List (List V)) : TimeM ℕ (V → ℕ) :=
  indexComponentsAuxM 0 comps (fun _ => 0)

section IndexComponents

variable [DecidableEq V] {adj : V → List V}

private theorem foldl_update_const (idx : ℕ) :
    ∀ (c : List V) (f : V → ℕ) (u : V),
      (c.foldl (fun f v => Function.update f v idx) f) u = if u ∈ c then idx else f u
  | [], f, u => by simp
  | v :: c, f, u => by
    rw [List.foldl_cons, foldl_update_const]
    by_cases huv : u = v
    · subst huv
      by_cases huc : u ∈ c <;> simp [huc]
    · simp [huv]

private theorem indexComponentsAux_notMem :
    ∀ (idx : ℕ) (cs : List (List V)) (f : V → ℕ) {u : V},
      u ∉ cs.flatten → indexComponentsAux idx cs f u = f u
  | _, [], f, _, _ => rfl
  | idx, c :: cs, f, u, hnu => by
    rw [List.flatten_cons, List.mem_append, not_or] at hnu
    rw [indexComponentsAux, indexComponentsAux_notMem (idx + 1) cs _ hnu.2,
      foldl_update_const, ite_eq_right (fun h => absurd h hnu.1)]

private theorem indexComponentsAux_getElem :
    ∀ (idx : ℕ) (cs : List (List V)) (f : V → ℕ),
      cs.flatten.Nodup →
      ∀ {i : ℕ} (hi : i < cs.length) {u : V}, u ∈ cs[i] →
        indexComponentsAux idx cs f u = idx + i
  | _, [], _, _, i, hi, _, _ => by simp at hi
  | idx, c :: cs, f, hnd, i, hi, u, hu => by
    rw [List.flatten_cons, List.nodup_append] at hnd
    cases i with
    | zero =>
      simp only [List.getElem_cons_zero] at hu
      have hnu : u ∉ cs.flatten := fun h => hnd.2.2 u hu u h rfl
      rw [indexComponentsAux, indexComponentsAux_notMem _ _ _ hnu, foldl_update_const,
        ite_eq_left hu]
      omega
    | succ i' =>
      simp only [List.length_cons, List.getElem_cons_succ] at hi hu
      rw [indexComponentsAux, indexComponentsAux_getElem (idx + 1) cs _ hnd.2.1 (by omega) hu]
      omega

theorem indexComponents_eq_of_mem {comps : List (List V)} (hnd : comps.flatten.Nodup)
    {i : ℕ} (hi : i < comps.length) {u : V} (hu : u ∈ comps[i]) :
    indexComponents comps u = i := by
  simpa [indexComponents] using indexComponentsAux_getElem 0 comps (fun _ => 0) hnd hi hu

private theorem indexComponentsAuxM_spec :
    ∀ (idx : ℕ) (cs : List (List V)) (f : V → ℕ),
      (indexComponentsAuxM idx cs f).ret = indexComponentsAux idx cs f ∧
      (indexComponentsAuxM idx cs f).time = cs.length + cs.flatten.length
  | _, [], f => by simp [indexComponentsAuxM, indexComponentsAux]
  | idx, c :: cs, f => by
    have hr₁ :
        (c.foldlM (fun f v => do ✓ return Function.update f v idx) f).ret =
          c.foldl (fun f v => Function.update f v idx) f := by
      simp [TimeM.ret_foldlM]
    have ht₁ :
        (c.foldlM (fun f v => do ✓ return Function.update f v idx) f).time = c.length := by
      simpa using TimeM.time_foldlM_of_time_eq
        (fun (f : V → ℕ) v => do ✓ return Function.update f v idx) c f (c := 1) (fun _ _ => rfl)
    obtain ⟨hr₂, ht₂⟩ := indexComponentsAuxM_spec (idx + 1) cs
      (c.foldl (fun f v => Function.update f v idx) f)
    simp only [indexComponentsAuxM, indexComponentsAux, TimeM.ret_bind, TimeM.time_bind,
      TimeM.time_tick, hr₁, hr₂, ht₁, ht₂, List.length_cons, List.flatten_cons, List.length_append,
      true_and]
    omega

theorem ret_indexComponentsM (comps : List (List V)) :
    (indexComponentsM comps).ret = indexComponents comps :=
  (indexComponentsAuxM_spec 0 comps (fun _ => 0)).1

theorem time_indexComponentsM (comps : List (List V)) :
    (indexComponentsM comps).time = comps.length + comps.flatten.length :=
  (indexComponentsAuxM_spec 0 comps (fun _ => 0)).2

namespace IsSCCCondensation

omit [DecidableEq V] in
theorem length_flatten_eq_card [Fintype V] {comps : List (List V)}
    (h : IsSCCCondensation adj comps) : comps.flatten.length = Fintype.card V := by
  classical
  rw [← List.toFinset_card_of_nodup h.nodup_flatten]
  congr 1
  ext v
  simp [h.mem_flatten v]

omit [DecidableEq V] in
theorem length_le_card [Fintype V] {comps : List (List V)}
    (h : IsSCCCondensation adj comps) : comps.length ≤ Fintype.card V := by
  have h1 : comps.length ≤ comps.flatten.length := by
    have hpos : ∀ c ∈ comps, 1 ≤ c.length := fun c hc =>
      List.length_pos_of_ne_nil (h.ne_nil c hc)
    clear h
    induction comps with
    | nil => simp
    | cons c cs ih =>
      have hc1 : 1 ≤ c.length := hpos c List.mem_cons_self
      have hcs := ih fun c' hc' => hpos c' (List.mem_cons_of_mem c hc')
      simp only [List.length_cons, List.flatten_cons, List.length_append]
      omega
  rwa [h.length_flatten_eq_card] at h1

theorem indexComponents_lt {comps : List (List V)} (h : IsSCCCondensation adj comps) (v : V) :
    indexComponents comps v < comps.length := by
  obtain ⟨c, hc, hv⟩ := List.mem_flatten.1 (h.mem_flatten v)
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
  rwa [indexComponents_eq_of_mem h.nodup_flatten hi hv]

theorem mem_getElem_indexComponents {comps : List (List V)} (h : IsSCCCondensation adj comps)
    (v : V) : v ∈ comps[indexComponents comps v]'(h.indexComponents_lt v) := by
  obtain ⟨c, hc, hv⟩ := List.mem_flatten.1 (h.mem_flatten v)
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
  have heq : indexComponents comps v = i := indexComponents_eq_of_mem h.nodup_flatten hi hv
  simpa [heq] using hv

theorem indexComponents_eq_iff {comps : List (List V)} (h : IsSCCCondensation adj comps)
    (u v : V) : indexComponents comps u = indexComponents comps v ↔ StronglyConnected adj u v := by
  rw [← h.same_comp_iff]
  constructor
  · intro heq
    refine ⟨comps[indexComponents comps u]'(h.indexComponents_lt u),
      List.getElem_mem (h.indexComponents_lt u), h.mem_getElem_indexComponents u, ?_⟩
    have hv := h.mem_getElem_indexComponents v
    simpa [← heq] using hv
  · rintro ⟨c, hc, hu, hv⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
    rw [indexComponents_eq_of_mem h.nodup_flatten hi hu,
      indexComponents_eq_of_mem h.nodup_flatten hi hv]

theorem indexComponents_le_of_edge {comps : List (List V)} (h : IsSCCCondensation adj comps)
    {u v : V} (huv : Edge adj u v) :
    indexComponents comps u ≤ indexComponents comps v :=
  h.condensation_le (h.indexComponents_lt u) (h.indexComponents_lt v)
    (h.mem_getElem_indexComponents u) (h.mem_getElem_indexComponents v) huv

theorem indexComponents_le_of_reach {comps : List (List V)} (h : IsSCCCondensation adj comps)
    {u v : V} (huv : Relation.ReflTransGen (Edge adj) u v) :
    indexComponents comps u ≤ indexComponents comps v := by
  induction huv with
  | refl => exact le_rfl
  | tail _ hbc ih => exact ih.trans (h.indexComponents_le_of_edge hbc)

theorem indexComponents_lt_of_edge {comps : List (List V)} (h : IsSCCCondensation adj comps)
    {u v : V} (huv : Edge adj u v) (hn : ¬ StronglyConnected adj u v) :
    indexComponents comps u < indexComponents comps v :=
  lt_of_le_of_ne (h.indexComponents_le_of_edge huv) fun heq =>
    hn ((h.indexComponents_eq_iff u v).1 heq)

end IsSCCCondensation

end IndexComponents

end Cslib.Algorithms.Lean.DFS
