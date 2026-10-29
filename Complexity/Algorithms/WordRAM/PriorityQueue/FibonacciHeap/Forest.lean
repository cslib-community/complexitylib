/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.PriorityQueue.FibonacciHeap.Trees

/-!
# Forest invariants and pure state transitions for a Fibonacci heap

This file lifts the single-tree model of `Trees.lean` to the full multi-root forest invariant
`FibRawInv` and proves the structural transitions required by all priority-queue operations:

* **Subtree cutting (`exists_parent_info`, `ValidSubtree.exists_cut`):** Severing a non-root node
  `cur` from its parent `p` splits `T` into a new valid root tree `T_cut` rooted at `cur` and a
  modified tree `T'` with `pending = some p` while preserving the multiset of tree nodes.
* **Full heap invariant (`FibRawInv`):** Relates `s : IndexedMinPQ.State n` to `st : RawState n`
  with exact domain, key, size, root-count, marked-count, `minRoot`, and `cons`-zeroing invariants,
  proving `IndexedMinPQ.findMin` agreement (`FibRawInv.findMin_eq_some`) and scalar bounds.
* **Transient cut invariant (`CutInv`):** Loop invariant for cascading cuts during `decreaseKey`,
  allowing a single `pending` ancestor whose child was just severed.

## Main definitions

* `Cslib.Algorithms.WordRAM.PriorityQueue.FibonacciHeap.FibRawInv`: full multi-root forest
  representation invariant relating `IndexedMinPQ.State n` to `RawState n`.
* `Cslib.Algorithms.WordRAM.PriorityQueue.FibonacciHeap.CutInv`: transient forest invariant during
  cascading cuts in `decreaseKey`.

## Main results

* `Cslib.Algorithms.WordRAM.PriorityQueue.FibonacciHeap.ValidSubtree.exists_cut`: severing a
  non-root node splits its enclosing tree into a valid root tree and a `pending`-parent tree.
* `Cslib.Algorithms.WordRAM.PriorityQueue.FibonacciHeap.FibRawInv.findMin_eq_some`: `minRoot`
  identifies the exact `IndexedMinPQ.findMin` element.

## References

* [M. L. Fredman and R. E. Tarjan, *Fibonacci Heaps and Their Uses in Improved Network Optimization
  Algorithms*][FredmanTarjan1987]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Chapter 19][CLRS2009]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.PriorityQueue.FibonacciHeap

open Cslib.Algorithms.Lean

/-! ## List surgery lemmas for child removal and replacement -/

theorem map_root_nodup {n : ℕ} {cs : List (FHTree n)} (hnd : (forestNodes cs).Nodup) :
    (cs.map FHTree.root).Nodup := by
  induction cs with
  | nil => exact List.nodup_nil
  | cons c rest ih =>
    simp only [forestNodes] at hnd
    obtain ⟨_, hnd_rest, hdisj⟩ := List.nodup_append.mp hnd
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih hnd_rest⟩
    intro hmem
    obtain ⟨c', hc', heq⟩ := List.mem_map.mp hmem
    exact hdisj c.root c.root_mem_nodes c'.root
      (mem_forestNodes_iff.mpr ⟨c', hc', c'.root_mem_nodes⟩) heq.symm

theorem forestNodes_nodup_idx_disjoint {n : ℕ} {cs : List (FHTree n)}
    (hnd : (forestNodes cs).Nodup) {i j : ℕ} (hi : i < cs.length) (hj : j < cs.length)
    (hij : i ≠ j) {x : Fin n} (hxi : x ∈ (cs[i]).nodes) (hxj : x ∈ (cs[j]).nodes) : False := by
  have hnd_roots : (cs.map FHTree.root).Nodup := map_root_nodup hnd
  have hne_tree : cs[i] ≠ cs[j] := by
    intro heq
    have hget : (cs.map FHTree.root)[i]'(by simp only [List.length_map]; exact hi) =
        (cs.map FHTree.root)[j]'(by simp only [List.length_map]; exact hj) := by
      simp only [List.getElem_map, heq]
    exact hij ((List.Nodup.getElem_inj_iff hnd_roots).mp hget)
  exact forestNodes_nodup_disjoint hnd (List.getElem_mem hi) (List.getElem_mem hj) hne_tree hxi hxj

private theorem mem_set_exists_idx {α : Type*} (L : List α) (i : ℕ) (v x : α)
    (h : x ∈ L.set i v) :
    x = v ∨ ∃ (j : ℕ) (hj : j < L.length), j ≠ i ∧ L[j] = x := by
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp h
  rw [List.length_set] at hj
  by_cases hji : j = i
  · subst hji; left; simp
  · right; refine ⟨j, hj, hji, ?_⟩; simp [List.getElem_set_ne (Ne.symm hji)]

theorem forestNodes_eraseIdx_perm {n : ℕ} :
    ∀ (cs : List (FHTree n)) (i : ℕ) (hi : i < cs.length),
      ((cs[i]).nodes ++ forestNodes (cs.eraseIdx i)).Perm (forestNodes cs)
  | [], _, hi => absurd hi (Nat.not_lt_zero _)
  | _ :: _, 0, _ => by
    simp only [List.getElem_cons_zero, List.eraseIdx_zero, forestNodes]
    exact List.Perm.refl _
  | c :: rest, i + 1, hi => by
    have hi' : i < rest.length := Nat.lt_of_succ_lt_succ hi
    simp only [List.getElem_cons_succ, List.eraseIdx_cons_succ, forestNodes]
    have ih := forestNodes_eraseIdx_perm rest i hi'
    have hswap : ((rest[i]).nodes ++ (c.nodes ++ forestNodes (rest.eraseIdx i))).Perm
        (c.nodes ++ ((rest[i]).nodes ++ forestNodes (rest.eraseIdx i))) := by
      rw [← List.append_assoc, ← List.append_assoc]
      exact List.Perm.append_right _ List.perm_append_comm
    exact hswap.trans (List.Perm.append_left c.nodes ih)

theorem forestNodes_set_perm {n : ℕ} :
    ∀ (cs : List (FHTree n)) (i : ℕ) (hi : i < cs.length) (T_cut c' : FHTree n),
      (T_cut.nodes ++ c'.nodes).Perm (cs[i]).nodes →
      (T_cut.nodes ++ forestNodes (cs.set i c')).Perm (forestNodes cs)
  | [], _, hi, _, _, _ => absurd hi (Nat.not_lt_zero _)
  | _ :: rest, 0, _, _, _, hp => by
    simp only [List.getElem_cons_zero, List.set_cons_zero, forestNodes, ← List.append_assoc] at hp ⊢
    exact List.Perm.append_right (forestNodes rest) hp
  | c :: rest, i + 1, hi, T_cut, c', hp => by
    have hi' : i < rest.length := Nat.lt_of_succ_lt_succ hi
    simp only [List.getElem_cons_succ, List.set_cons_succ, forestNodes] at hp ⊢
    have ih := forestNodes_set_perm rest i hi' T_cut c' hp
    have hswap : (T_cut.nodes ++ (c.nodes ++ forestNodes (rest.set i c'))).Perm
        (c.nodes ++ (T_cut.nodes ++ forestNodes (rest.set i c'))) := by
      rw [← List.append_assoc, ← List.append_assoc]
      exact List.Perm.append_right _ List.perm_append_comm
    exact hswap.trans (List.Perm.append_left c.nodes ih)

theorem map_root_set_eq {n : ℕ} :
    ∀ (cs : List (FHTree n)) (i : ℕ) (hi : i < cs.length) (c' : FHTree n),
      c'.root = (cs[i]).root → (cs.set i c').map FHTree.root = cs.map FHTree.root
  | [], _, hi, _, _ => absurd hi (Nat.not_lt_zero _)
  | _ :: rest, 0, _, c', hr => by
    simp only [List.getElem_cons_zero, List.set_cons_zero, List.map_cons, hr]
  | c :: rest, i + 1, hi, c', hr => by
    have hi' : i < rest.length := Nat.lt_of_succ_lt_succ hi
    simp only [List.getElem_cons_succ, List.set_cons_succ, List.map_cons] at hr ⊢
    rw [map_root_set_eq rest i hi' c' hr]

/-! ## Parent witnesses and subtree cutting -/

/-- Every strict descendant `x` of `T` has `st.par x = q.val + 1` for some `q ∈ T.nodes`. -/
theorem ValidSubtree.par_of_mem_children {n : ℕ} {st : RawState n} {pending : Option (Fin n)}
    {T : FHTree n} (hT : ValidSubtree st pending T) :
    ∀ x ∈ forestNodes T.children, ∃ q ∈ T.nodes, st.par x = q.val + 1 := by
  induction hT with
  | @mk u cs _ _ _ _ hpar _ _ _ ih =>
    intro x hx
    obtain ⟨c, hc, hxc⟩ := mem_forestNodes_iff.mp hx
    rw [c.nodes_eq] at hxc
    rcases List.mem_cons.mp hxc with rfl | hdesc
    · exact ⟨u, List.mem_cons_self, hpar c hc⟩
    · obtain ⟨q, hq, hpq⟩ := ih c hc x hdesc
      exact ⟨q, List.mem_cons_of_mem u (mem_forestNodes_iff.mpr ⟨c, hc, hq⟩), hpq⟩

/-- Updating only the root's `mark` to a value `≤ 1` while keeping all other subtree fields fixed
preserves `ValidSubtree`. -/
theorem ValidSubtree.frame_root_mark {n : ℕ} {st st' : RawState n}
    {pending pending' : Option (Fin n)}
    {T : FHTree n} (hT : ValidSubtree st pending T) (hnd : T.nodes.Nodup)
    (hrm : st'.mark T.root ≤ 1)
    (hroot : st'.inHeap T.root = st.inHeap T.root ∧ st'.deg T.root = st.deg T.root ∧
      st'.child T.root = st.child T.root ∧ st'.key T.root = st.key T.root)
    (hdesc_node : ∀ x ∈ forestNodes T.children,
      st'.inHeap x = st.inHeap x ∧ st'.mark x = st.mark x ∧ st'.deg x = st.deg x ∧
      st'.child x = st.child x ∧ st'.key x = st.key x)
    (hdesc_ptr : ∀ x ∈ forestNodes T.children,
      st'.par x = st.par x ∧ st'.left x = st.left x ∧ st'.right x = st.right x ∧
      ((some x = pending') ↔ (some x = pending))) :
    ValidSubtree st' pending' T := by
  cases hT with
  | @mk u cs hin _ hdeg hchild hpar hprio hrank hsub =>
    simp only [FHTree.root_node, FHTree.children_node] at hrm hroot hdesc_node hdesc_ptr
    have hc_desc : ∀ c ∈ cs, c.root ∈ forestNodes cs := fun c hc =>
      mem_forestNodes_iff.mpr ⟨c, hc, c.root_mem_nodes⟩
    refine ⟨hroot.1.trans_ne hin, hrm, hroot.2.1.trans hdeg, ?_, ?_, ?_, ?_, ?_⟩
    · rcases hchild with ⟨rfl, hc0⟩ | ⟨h, tail, hcu, hcirc, hperm⟩
      · exact Or.inl ⟨rfl, hroot.2.2.1.trans hc0⟩
      · refine Or.inr ⟨h, tail, hroot.2.2.1.trans hcu, hcirc.frame fun x hx => ?_, hperm⟩
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp (hperm.subset hx)
        have hd := hdesc_ptr c.root (hc_desc c hc)
        exact ⟨hd.2.1, hd.2.2.1⟩
    · intro c hc
      exact (hdesc_ptr c.root (hc_desc c hc)).1.trans (hpar c hc)
    · intro c hc
      rw [hroot.2.2.2, (hdesc_node c.root (hc_desc c hc)).2.2.2.2]
      exact hprio c hc
    · intro i hi
      have hmem : cs[i] ∈ cs := List.getElem_mem hi
      have hcn := hdesc_node (cs[i]).root (hc_desc cs[i] hmem)
      have hiff := (hdesc_ptr (cs[i]).root (hc_desc cs[i] hmem)).2.2.2
      have hite : (if some (cs[i]).root = pending' then 1 else 0) =
          (if some (cs[i]).root = pending then 1 else 0) := by
        simp only [hiff]
      rw [hcn.2.2.1, hcn.2.1, hite]
      exact hrank i hi
    · intro c hc
      exact (hsub c hc).frame
        (fun x hx => hdesc_node x (mem_forestNodes_iff.mpr ⟨c, hc, hx⟩))
        (fun x hx => hdesc_ptr x
          (mem_forestNodes_iff.mpr ⟨c, hc, c.nodes_eq ▸ List.mem_cons_of_mem c.root hx⟩))

/-- Pre-cut structural properties of `cur` and its parent `p` inside any valid subtree containing
`cur` as a strict descendant. -/
theorem exists_parent_info {n : ℕ} {st : RawState n} {pending : Option (Fin n)} {T : FHTree n}
    (hT : ValidSubtree st pending T) {cur p : Fin n}
    (hcur : cur ∈ forestNodes T.children) (hpar_cur : st.par cur = p.val + 1) :
    p ∈ T.nodes ∧ st.inHeap p ≠ 0 ∧ st.mark p ≤ 1 ∧ st.inHeap cur ≠ 0 ∧ st.mark cur ≤ 1 ∧
    1 ≤ st.deg p ∧
    (2 ≤ st.deg p →
      ∃ (h : Fin n) (tail : List (Fin n)),
        st.child p = h.val + 1 ∧
        IsCircList st.left st.right (h :: tail) ∧
        cur ∈ h :: tail ∧ 2 ≤ (h :: tail).length ∧
        ∀ x ∈ h :: tail, st.par x = p.val + 1) := by
  induction hT with
  | @mk u cs hin hmark hdeg hchild hpar _ _ hsub ih =>
    simp only [FHTree.children_node] at hcur
    obtain ⟨c, hc, hx_c⟩ := mem_forestNodes_iff.mp hcur
    have hc_sub := hsub c hc
    cases hc_eq : c with
    | node w cs_w =>
      rw [hc_eq] at hc hx_c hc_sub
      rcases List.mem_cons.mp hx_c with rfl | hdesc_w
      · have hup : u = p := Fin.ext (by
          have hp_c := hpar (.node cur cs_w) hc
          simp only [FHTree.root_node] at hp_c
          omega)
        subst hup
        rcases hc_sub with ⟨hin_cur, hm_cur, _, _, _, _, _, _⟩
        have hlen_pos : 1 ≤ cs.length := by
          cases cs with
          | nil => exact absurd hc List.not_mem_nil
          | cons _ _ => simp only [List.length_cons]; omega
        refine ⟨List.mem_cons_self, hin, hmark, hin_cur, hm_cur, by omega, fun hdeg2 => ?_⟩
        rcases hchild with ⟨rfl, _⟩ | ⟨h, tail, hcu, hcirc, hperm⟩
        · simp only [List.length_nil] at hdeg; omega
        · have hcur_map : cur ∈ cs.map FHTree.root :=
            List.mem_map.mpr ⟨.node cur cs_w, hc, rfl⟩
          have hcur_ht : cur ∈ h :: tail := hperm.symm.subset hcur_map
          have hht_len : (h :: tail).length = cs.length :=
            hperm.length_eq.trans (List.length_map _)
          refine ⟨h, tail, hcu, hcirc, hcur_ht, by omega, fun x hx => ?_⟩
          obtain ⟨c', hc', rfl⟩ := List.mem_map.mp (hperm.subset hx)
          exact hpar c' hc'
      · obtain ⟨hp_in, hin_p, hm_p, hin_cur, hm_cur, hd1, hd2⟩ := ih (.node w cs_w) hc hdesc_w
        exact ⟨List.mem_cons_of_mem u (mem_forestNodes_iff.mpr ⟨.node w cs_w, hc, hp_in⟩),
          hin_p, hm_p, hin_cur, hm_cur, hd1, hd2⟩

/-- Cutting a strict descendant `cur` (with `st.par cur = p.val + 1`) from `T` splits `T` into a
new root tree `T_cut` (`T_cut.root = cur`) and a pruned tree `T'` (`T'.root = T.root`,
`p ∈ T'.nodes`) satisfying `ValidRoot st' none T_cut` and `ValidSubtree st' (some p) T'`. -/
theorem ValidSubtree.exists_cut {n : ℕ} {st st' : RawState n} {pending : Option (Fin n)}
    {T : FHTree n} (hT : ValidSubtree st pending T) (hnd : T.nodes.Nodup)
    {cur p : Fin n} (hcur : cur ∈ forestNodes T.children) (hpar_cur : st.par cur = p.val + 1)
    (hpend : pending = none ∨ pending = some cur)
    (hin_eq : ∀ x ∈ T.nodes, st'.inHeap x = st.inHeap x ∧ st'.key x = st.key x)
    (hmark' : st'.mark cur = 0 ∧ ∀ x ∈ T.nodes, x ≠ cur → st'.mark x = st.mark x)
    (hdeg' : st'.deg p + 1 = st.deg p ∧ ∀ x ∈ T.nodes, x ≠ p → st'.deg x = st.deg x)
    (hpar' : st'.par cur = 0 ∧ ∀ x ∈ T.nodes, x ≠ cur → st'.par x = st.par x)
    (hchild_p :
      (st.deg p = 1 → st'.child p = 0) ∧
      (∀ (h : Fin n) (tail : List (Fin n)),
        2 ≤ st.deg p → st.child p = h.val + 1 →
        IsCircList st.left st.right (h :: tail) → cur ∈ h :: tail →
        ∃ (r : Fin n) (rest : List (Fin n)),
          st'.child p = r.val + 1 ∧
          IsCircList st'.left st'.right (r :: rest) ∧
          (r :: rest).Perm ((h :: tail).erase cur)))
    (hchild_other : ∀ x ∈ T.nodes, x ≠ p → st'.child x = st.child x)
    (hlr_other : ∀ x ∈ T.nodes, st.par x ≠ p.val + 1 → st.par x ≠ 0 →
      st'.left x = st.left x ∧ st'.right x = st.right x) :
    ∃ (T_cut T' : FHTree n),
      T_cut.root = cur ∧ T'.root = T.root ∧ p ∈ T'.nodes ∧
      (T_cut.nodes ++ T'.nodes).Perm T.nodes ∧
      ValidRoot st' none T_cut ∧
      ValidSubtree st' (some p) T' := by
  induction hT with
  | @mk u cs hin hmark hdeg hchild hpar hprio hrank hsub ih =>
    simp only [FHTree.children_node] at hcur
    have hnd_u : u ∉ forestNodes cs := (List.nodup_cons.mp hnd).1
    have hnd_cs : (forestNodes cs).Nodup := (List.nodup_cons.mp hnd).2
    obtain ⟨cw, hcw_mem, hx_in_cw⟩ := mem_forestNodes_iff.mp hcur
    obtain ⟨i, hi, hci_cw⟩ := List.mem_iff_getElem.mp hcw_mem
    subst hci_cw
    have hi_mem : cs[i] ∈ cs := List.getElem_mem hi
    have hnd_ci : (cs[i]).nodes.Nodup := forestNodes_nodup_tree hnd_cs hi_mem
    by_cases hroot_eq : (cs[i]).root = cur
    · have hup : u = p := Fin.ext (by
        have hp_i := hpar cs[i] hi_mem
        rw [hroot_eq] at hp_i
        omega)
      subst hup
      have hperm_nodes :
          ((cs[i]).nodes ++ (FHTree.node u (cs.eraseIdx i)).nodes).Perm
            (FHTree.node u cs).nodes := by
        simp only [FHTree.nodes]
        exact List.perm_middle.trans (List.Perm.cons u (forestNodes_eraseIdx_perm cs i hi))
      have hu_ne_cur : u ≠ cur := fun e => hnd_u (e ▸ hcur)
      have hu_in : u ∈ (FHTree.node u cs).nodes := List.mem_cons_self
      have hcur_in : cur ∈ (FHTree.node u cs).nodes := List.mem_cons_of_mem u hcur
      have hu_not_ci : u ∉ (cs[i]).nodes := fun hm =>
        hnd_u (mem_forestNodes_iff.mpr ⟨cs[i], hi_mem, hm⟩)
      have hcur_not_desc : cur ∉ forestNodes (cs[i]).children := by
        rw [(cs[i]).nodes_eq, hroot_eq] at hnd_ci
        exact (List.nodup_cons.mp hnd_ci).1
      have hsub_ci_none : ValidSubtree st none cs[i] := by
        rcases hpend with rfl | rfl
        · exact hsub cs[i] hi_mem
        · exact (hsub cs[i] hi_mem).clear_pending hcur_not_desc
      have hcut_root : ValidRoot st' none cs[i] := by
        refine ⟨hsub_ci_none.frame_root_mark hnd_ci (by rw [hroot_eq, hmark'.1]; omega) ?_ ?_ ?_,
          by rw [hroot_eq]; exact hpar'.1, by rw [hroot_eq]; exact hmark'.1⟩
        · rw [hroot_eq]
          exact ⟨(hin_eq cur hcur_in).1, hdeg'.2 cur hcur_in hu_ne_cur.symm,
            hchild_other cur hcur_in hu_ne_cur.symm, (hin_eq cur hcur_in).2⟩
        · intro x hx
          have hx_ci : x ∈ (cs[i]).nodes :=
            (cs[i]).nodes_eq ▸ List.mem_cons_of_mem (cs[i]).root hx
          have hx_in : x ∈ (FHTree.node u cs).nodes :=
            List.mem_cons_of_mem u (mem_forestNodes_iff.mpr ⟨cs[i], hi_mem, hx_ci⟩)
          have hx_ne_cur : x ≠ cur := fun e => hcur_not_desc (e ▸ hx)
          have hx_ne_u : x ≠ u := fun e => hu_not_ci (e ▸ hx_ci)
          exact ⟨(hin_eq x hx_in).1, hmark'.2 x hx_in hx_ne_cur, hdeg'.2 x hx_in hx_ne_u,
            hchild_other x hx_in hx_ne_u, (hin_eq x hx_in).2⟩
        · intro x hx
          have hx_ci : x ∈ (cs[i]).nodes :=
            (cs[i]).nodes_eq ▸ List.mem_cons_of_mem (cs[i]).root hx
          have hx_in : x ∈ (FHTree.node u cs).nodes :=
            List.mem_cons_of_mem u (mem_forestNodes_iff.mpr ⟨cs[i], hi_mem, hx_ci⟩)
          have hx_ne_cur : x ≠ cur := fun e => hcur_not_desc (e ▸ hx)
          obtain ⟨q, hq_ci, hpq⟩ := hsub_ci_none.par_of_mem_children x hx
          have hq_ne_u : q ≠ u := fun e => hu_not_ci (e ▸ hq_ci)
          have hlr := hlr_other x hx_in (by omega) (by omega)
          exact ⟨hpar'.2 x hx_in hx_ne_cur, hlr.1, hlr.2, Iff.rfl⟩
      refine ⟨cs[i], .node u (cs.eraseIdx i), hroot_eq, rfl, List.mem_cons_self,
        hperm_nodes, hcut_root, ?_⟩
      have hlen_er : (cs.eraseIdx i).length + 1 = cs.length := by
        rw [List.length_eraseIdx_of_lt hi]
        omega
      refine ⟨(hin_eq u hu_in).1.trans_ne hin,
        by rw [hmark'.2 u hu_in hu_ne_cur]; exact hmark,
        by omega, ?_, ?_, ?_, ?_, ?_⟩
      · by_cases hd1 : st.deg u = 1
        · have hcs_er_nil : cs.eraseIdx i = [] :=
            List.length_eq_zero_iff.mp (by omega)
          exact Or.inl ⟨hcs_er_nil, hchild_p.1 hd1⟩
        · have hd2 : 2 ≤ st.deg u := by omega
          rcases hchild with ⟨rfl, _⟩ | ⟨h, tail, hcu, hcirc, hperm⟩
          · simp only [List.length_nil] at hdeg; omega
          · have hcur_map : cur ∈ cs.map FHTree.root :=
              hroot_eq ▸ List.mem_map_of_mem hi_mem
            have hcur_ht : cur ∈ h :: tail := hperm.symm.subset hcur_map
            obtain ⟨r, rest, hch_u', hcirc', hperm_er⟩ :=
              hchild_p.2 h tail hd2 hcu hcirc hcur_ht
            have hmap_er : (cs.eraseIdx i).map FHTree.root = (cs.map FHTree.root).erase cur := by
              rw [← List.eraseIdx_map]
              have hlen_m : i < (cs.map FHTree.root).length := by
                simp only [List.length_map]; exact hi
              have hget_m : (cs.map FHTree.root)[i]'hlen_m = cur := by
                simp only [List.getElem_map, hroot_eq]
              rw [← (map_root_nodup hnd_cs).erase_getElem i hlen_m, hget_m]
            exact Or.inr ⟨r, rest, hch_u', hcirc',
              hperm_er.trans (hmap_er ▸ hperm.erase cur)⟩
      · intro T_c hTc
        obtain ⟨j, hj, hji, rfl⟩ := List.mem_eraseIdx_iff_getElem.mp hTc
        have hr_ne_cur : (cs[j]).root ≠ cur := fun e =>
          forestNodes_nodup_idx_disjoint hnd_cs hi hj hji.symm
            (hroot_eq ▸ (cs[i]).root_mem_nodes) (e ▸ (cs[j]).root_mem_nodes)
        have hr_in : (cs[j]).root ∈ (FHTree.node u cs).nodes :=
          List.mem_cons_of_mem u
            (mem_forestNodes_iff.mpr ⟨cs[j], List.getElem_mem hj, (cs[j]).root_mem_nodes⟩)
        exact (hpar'.2 (cs[j]).root hr_in hr_ne_cur).trans (hpar cs[j] (List.getElem_mem hj))
      · intro T_c hTc
        obtain ⟨j, hj, _, rfl⟩ := List.mem_eraseIdx_iff_getElem.mp hTc
        have hr_in : (cs[j]).root ∈ (FHTree.node u cs).nodes :=
          List.mem_cons_of_mem u
            (mem_forestNodes_iff.mpr ⟨cs[j], List.getElem_mem hj, (cs[j]).root_mem_nodes⟩)
        rw [(hin_eq u hu_in).2, (hin_eq (cs[j]).root hr_in).2]
        exact hprio cs[j] (List.getElem_mem hj)
      · intro j hj
        rw [List.getElem_eraseIdx]
        by_cases hji : j < i
        · simp only [hji, ↓reduceDIte]
          have hj_lt : j < cs.length := Nat.lt_trans hji hi
          have hji_ne : i ≠ j := Nat.ne_of_gt hji
          have hr_ne_cur : (cs[j]).root ≠ cur := fun e =>
            forestNodes_nodup_idx_disjoint hnd_cs hi hj_lt hji_ne
              (hroot_eq ▸ (cs[i]).root_mem_nodes) (e ▸ (cs[j]).root_mem_nodes)
          have hr_desc : (cs[j]).root ∈ forestNodes cs :=
            mem_forestNodes_iff.mpr ⟨cs[j], List.getElem_mem hj_lt, (cs[j]).root_mem_nodes⟩
          have hr_ne_u : (cs[j]).root ≠ u := fun e => hnd_u (e ▸ hr_desc)
          have hr_in : (cs[j]).root ∈ (FHTree.node u cs).nodes := List.mem_cons_of_mem u hr_desc
          have hr_old := hrank j hj_lt
          have hpend_0 : (if some (cs[j]).root = pending then 1 else 0) = 0 := by
            rcases hpend with rfl | rfl
            · simp only [reduceCtorEq, ↓reduceIte]
            · simp only [Option.some.injEq, hr_ne_cur, ↓reduceIte]
          rw [hpend_0] at hr_old
          rw [hdeg'.2 (cs[j]).root hr_in hr_ne_u, hmark'.2 (cs[j]).root hr_in hr_ne_cur]
          omega
        · simp only [hji, ↓reduceDIte]
          have hj1_lt : j + 1 < cs.length := by omega
          have hji_ne : i ≠ j + 1 := by omega
          have hr_ne_cur : (cs[j + 1]).root ≠ cur := fun e =>
            forestNodes_nodup_idx_disjoint hnd_cs hi hj1_lt hji_ne
              (hroot_eq ▸ (cs[i]).root_mem_nodes) (e ▸ (cs[j + 1]).root_mem_nodes)
          have hr_desc : (cs[j + 1]).root ∈ forestNodes cs :=
            mem_forestNodes_iff.mpr
              ⟨cs[j + 1], List.getElem_mem hj1_lt, (cs[j + 1]).root_mem_nodes⟩
          have hr_ne_u : (cs[j + 1]).root ≠ u := fun e => hnd_u (e ▸ hr_desc)
          have hr_in : (cs[j + 1]).root ∈ (FHTree.node u cs).nodes := List.mem_cons_of_mem u hr_desc
          have hr_old := hrank (j + 1) hj1_lt
          have hpend_0 : (if some (cs[j + 1]).root = pending then 1 else 0) = 0 := by
            rcases hpend with rfl | rfl
            · simp only [reduceCtorEq, ↓reduceIte]
            · simp only [Option.some.injEq, hr_ne_cur, ↓reduceIte]
          rw [hpend_0] at hr_old
          rw [hdeg'.2 (cs[j + 1]).root hr_in hr_ne_u, hmark'.2 (cs[j + 1]).root hr_in hr_ne_cur]
          omega
      · intro T_c hTc
        obtain ⟨j, hj, hji, rfl⟩ := List.mem_eraseIdx_iff_getElem.mp hTc
        have hcur_not_cj : cur ∉ (cs[j]).nodes := fun hm =>
          forestNodes_nodup_idx_disjoint hnd_cs hi hj hji.symm hx_in_cw hm
        have hu_not_cj : u ∉ (cs[j]).nodes := fun hm =>
          hnd_u (mem_forestNodes_iff.mpr ⟨cs[j], List.getElem_mem hj, hm⟩)
        have hsub_j_none : ValidSubtree st none cs[j] := by
          rcases hpend with rfl | rfl
          · exact hsub cs[j] (List.getElem_mem hj)
          · exact (hsub cs[j] (List.getElem_mem hj)).clear_pending fun hm =>
              hcur_not_cj ((cs[j]).nodes_eq ▸ List.mem_cons_of_mem _ hm)
        refine (hsub_j_none.frame (pending' := none) (fun x hx => ?_)
          (fun x hx => ?_)).weaken_pending (some u)
        · have hx_in : x ∈ (FHTree.node u cs).nodes :=
            List.mem_cons_of_mem u (mem_forestNodes_iff.mpr ⟨cs[j], List.getElem_mem hj, hx⟩)
          have hx_ne_cur : x ≠ cur := fun e => hcur_not_cj (e ▸ hx)
          have hx_ne_u : x ≠ u := fun e => hu_not_cj (e ▸ hx)
          exact ⟨(hin_eq x hx_in).1, hmark'.2 x hx_in hx_ne_cur, hdeg'.2 x hx_in hx_ne_u,
            hchild_other x hx_in hx_ne_u, (hin_eq x hx_in).2⟩
        · have hx_cj : x ∈ (cs[j]).nodes :=
            (cs[j]).nodes_eq ▸ List.mem_cons_of_mem (cs[j]).root hx
          have hx_in : x ∈ (FHTree.node u cs).nodes :=
            List.mem_cons_of_mem u (mem_forestNodes_iff.mpr ⟨cs[j], List.getElem_mem hj, hx_cj⟩)
          have hx_ne_cur : x ≠ cur := fun e => hcur_not_cj (e ▸ hx_cj)
          obtain ⟨q, hq_cj, hpq⟩ := hsub_j_none.par_of_mem_children x hx
          have hq_ne_u : q ≠ u := fun e => hu_not_cj (e ▸ hq_cj)
          have hlr := hlr_other x hx_in (by omega) (by omega)
          exact ⟨hpar'.2 x hx_in hx_ne_cur, hlr.1, hlr.2, Iff.rfl⟩
    · have hcur_desc_ci : cur ∈ forestNodes (cs[i]).children := by
        rw [(cs[i]).nodes_eq] at hx_in_cw
        exact (List.mem_cons.mp hx_in_cw).resolve_left (Ne.symm hroot_eq)
      have sub_in : ∀ x ∈ (cs[i]).nodes, x ∈ (FHTree.node u cs).nodes := fun x hx =>
        List.mem_cons_of_mem u (mem_forestNodes_iff.mpr ⟨cs[i], hi_mem, hx⟩)
      obtain ⟨T_cut, c', hcut_r, hc'_r, hp_in_c', hperm_ci, hvalid_cut, hvalid_c'⟩ :=
        ih cs[i] hi_mem hnd_ci hcur_desc_ci
          (fun x hx => hin_eq x (sub_in x hx))
          ⟨hmark'.1, fun x hx => hmark'.2 x (sub_in x hx)⟩
          ⟨hdeg'.1, fun x hx => hdeg'.2 x (sub_in x hx)⟩
          ⟨hpar'.1, fun x hx => hpar'.2 x (sub_in x hx)⟩
          (fun x hx => hchild_other x (sub_in x hx))
          (fun x hx => hlr_other x (sub_in x hx))
      have hp_in_ci : p ∈ (cs[i]).nodes :=
        hperm_ci.subset (List.mem_append_right _ hp_in_c')
      have hu_ne_p : u ≠ p := fun e =>
        hnd_u (e ▸ mem_forestNodes_iff.mpr ⟨cs[i], hi_mem, hp_in_ci⟩)
      have hu_ne_cur : u ≠ cur := fun e => hnd_u (e ▸ hcur)
      have hu_in : u ∈ (FHTree.node u cs).nodes := List.mem_cons_self
      have hperm_nodes :
          (T_cut.nodes ++ (FHTree.node u (cs.set i c')).nodes).Perm
            (FHTree.node u cs).nodes := by
        simp only [FHTree.nodes]
        exact List.perm_middle.trans
          (List.Perm.cons u (forestNodes_set_perm cs i hi T_cut c' hperm_ci))
      have hc'_mem_set : c' ∈ cs.set i c' :=
        List.mem_iff_getElem.mpr
          ⟨i, by simp only [List.length_set]; exact hi, by simp only [List.getElem_set_self]⟩
      have hp_in_T' : p ∈ (FHTree.node u (cs.set i c')).nodes :=
        List.mem_cons_of_mem u (mem_forestNodes_iff.mpr ⟨c', hc'_mem_set, hp_in_c'⟩)
      refine ⟨T_cut, .node u (cs.set i c'), hcut_r, rfl, hp_in_T', hperm_nodes, hvalid_cut, ?_⟩
      refine ⟨(hin_eq u hu_in).1.trans_ne hin,
        by rw [hmark'.2 u hu_in hu_ne_cur]; exact hmark,
        by rw [hdeg'.2 u hu_in hu_ne_p, List.length_set]; exact hdeg, ?_, ?_, ?_, ?_, ?_⟩
      · rcases hchild with ⟨rfl, hc0⟩ | ⟨h, tail, hcu, hcirc, hperm⟩
        · exact absurd hi (Nat.not_lt_zero _)
        · refine Or.inr ⟨h, tail, (hchild_other u hu_in hu_ne_p).trans hcu,
            hcirc.frame fun x hx => ?_, ?_⟩
          · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp (hperm.subset hx)
            have hc_par : st.par c.root = u.val + 1 := hpar c hc
            have hc_in : c.root ∈ (FHTree.node u cs).nodes :=
              List.mem_cons_of_mem u (mem_forestNodes_iff.mpr ⟨c, hc, c.root_mem_nodes⟩)
            exact hlr_other c.root hc_in (by have := Fin.val_ne_of_ne hu_ne_p; omega) (by omega)
          · rw [map_root_set_eq cs i hi c' hc'_r]
            exact hperm
      · intro T_c hTc
        rcases mem_set_exists_idx cs i c' T_c hTc with rfl | ⟨j, hj, hji, rfl⟩
        · rw [hc'_r]
          have hr_in : (cs[i]).root ∈ (FHTree.node u cs).nodes := sub_in _ (cs[i]).root_mem_nodes
          exact (hpar'.2 (cs[i]).root hr_in hroot_eq).trans (hpar cs[i] hi_mem)
        · have hr_ne_cur : (cs[j]).root ≠ cur := fun e =>
            forestNodes_nodup_idx_disjoint hnd_cs hi hj hji.symm hx_in_cw
              (e ▸ (cs[j]).root_mem_nodes)
          have hr_in : (cs[j]).root ∈ (FHTree.node u cs).nodes :=
            List.mem_cons_of_mem u
              (mem_forestNodes_iff.mpr ⟨cs[j], List.getElem_mem hj, (cs[j]).root_mem_nodes⟩)
          exact (hpar'.2 (cs[j]).root hr_in hr_ne_cur).trans (hpar cs[j] (List.getElem_mem hj))
      · intro T_c hTc
        rcases mem_set_exists_idx cs i c' T_c hTc with rfl | ⟨j, hj, _, rfl⟩
        · rw [hc'_r]
          have hr_in : (cs[i]).root ∈ (FHTree.node u cs).nodes := sub_in _ (cs[i]).root_mem_nodes
          rw [(hin_eq u hu_in).2, (hin_eq (cs[i]).root hr_in).2]
          exact hprio cs[i] hi_mem
        · have hr_in : (cs[j]).root ∈ (FHTree.node u cs).nodes :=
            List.mem_cons_of_mem u
              (mem_forestNodes_iff.mpr ⟨cs[j], List.getElem_mem hj, (cs[j]).root_mem_nodes⟩)
          rw [(hin_eq u hu_in).2, (hin_eq (cs[j]).root hr_in).2]
          exact hprio cs[j] (List.getElem_mem hj)
      · intro j hj_set
        have hj : j < cs.length := by simpa only [List.length_set] using hj_set
        by_cases hji : j = i
        · subst hji
          rw [List.getElem_set_self, hc'_r]
          have hr_in : (cs[j]).root ∈ (FHTree.node u cs).nodes := sub_in _ (cs[j]).root_mem_nodes
          have hr_old := hrank j hj
          have hpend_0 : (if some (cs[j]).root = pending then 1 else 0) = 0 := by
            rcases hpend with rfl | rfl
            · simp only [reduceCtorEq, ↓reduceIte]
            · simp only [Option.some.injEq, hroot_eq, ↓reduceIte]
          rw [hpend_0] at hr_old
          rw [hmark'.2 (cs[j]).root hr_in hroot_eq]
          by_cases hwp : (cs[j]).root = p
          · rw [hwp] at hr_old ⊢
            simp only [↓reduceIte]
            omega
          · simp only [Option.some.injEq, hwp, ↓reduceIte]
            rw [hdeg'.2 (cs[j]).root hr_in hwp]
            omega
        · rw [List.getElem_set_ne (Ne.symm hji)]
          have hr_ne_cur : (cs[j]).root ≠ cur := fun e =>
            forestNodes_nodup_idx_disjoint hnd_cs hj hi hji (e ▸ (cs[j]).root_mem_nodes) hx_in_cw
          have hr_ne_p : (cs[j]).root ≠ p := fun e =>
            forestNodes_nodup_idx_disjoint hnd_cs hj hi hji (e ▸ (cs[j]).root_mem_nodes) hp_in_ci
          have hr_in : (cs[j]).root ∈ (FHTree.node u cs).nodes :=
            List.mem_cons_of_mem u
              (mem_forestNodes_iff.mpr ⟨cs[j], List.getElem_mem hj, (cs[j]).root_mem_nodes⟩)
          have hr_old := hrank j hj
          have hpend_0 : (if some (cs[j]).root = pending then 1 else 0) = 0 := by
            rcases hpend with rfl | rfl
            · simp only [reduceCtorEq, ↓reduceIte]
            · simp only [Option.some.injEq, hr_ne_cur, ↓reduceIte]
          rw [hpend_0] at hr_old
          rw [hdeg'.2 (cs[j]).root hr_in hr_ne_p, hmark'.2 (cs[j]).root hr_in hr_ne_cur]
          omega
      · intro T_c hTc
        rcases mem_set_exists_idx cs i c' T_c hTc with rfl | ⟨j, hj, hji, rfl⟩
        · exact hvalid_c'
        · have hcur_not_cj : cur ∉ (cs[j]).nodes := fun hm =>
            forestNodes_nodup_idx_disjoint hnd_cs hi hj hji.symm hx_in_cw hm
          have hp_not_cj : p ∉ (cs[j]).nodes := fun hm =>
            forestNodes_nodup_idx_disjoint hnd_cs hi hj hji.symm hp_in_ci hm
          have hsub_j_none : ValidSubtree st none cs[j] := by
            rcases hpend with rfl | rfl
            · exact hsub cs[j] (List.getElem_mem hj)
            · exact (hsub cs[j] (List.getElem_mem hj)).clear_pending fun hm =>
                hcur_not_cj ((cs[j]).nodes_eq ▸ List.mem_cons_of_mem _ hm)
          refine (hsub_j_none.frame (pending' := none) (fun x hx => ?_)
            (fun x hx => ?_)).weaken_pending (some p)
          · have hx_in : x ∈ (FHTree.node u cs).nodes :=
              List.mem_cons_of_mem u (mem_forestNodes_iff.mpr ⟨cs[j], List.getElem_mem hj, hx⟩)
            have hx_ne_cur : x ≠ cur := fun e => hcur_not_cj (e ▸ hx)
            have hx_ne_p : x ≠ p := fun e => hp_not_cj (e ▸ hx)
            exact ⟨(hin_eq x hx_in).1, hmark'.2 x hx_in hx_ne_cur, hdeg'.2 x hx_in hx_ne_p,
              hchild_other x hx_in hx_ne_p, (hin_eq x hx_in).2⟩
          · have hx_cj : x ∈ (cs[j]).nodes :=
              (cs[j]).nodes_eq ▸ List.mem_cons_of_mem (cs[j]).root hx
            have hx_in : x ∈ (FHTree.node u cs).nodes :=
              List.mem_cons_of_mem u (mem_forestNodes_iff.mpr ⟨cs[j], List.getElem_mem hj, hx_cj⟩)
            have hx_ne_cur : x ≠ cur := fun e => hcur_not_cj (e ▸ hx_cj)
            obtain ⟨q, hq_cj, hpq⟩ := hsub_j_none.par_of_mem_children x hx
            have hq_ne_p : q ≠ p := fun e => hp_not_cj (e ▸ hq_cj)
            have hlr := hlr_other x hx_in (by have := Fin.val_ne_of_ne hq_ne_p; omega) (by omega)
            exact ⟨hpar'.2 x hx_in hx_ne_cur, hlr.1, hlr.2, Iff.rfl⟩

/-- Marking an unmarked `pending = some z` node (`st.mark z = 0`, `st'.mark z = 1`) absorbs the
transient rank slack and restores `ValidSubtree st' none T`. -/
theorem ValidSubtree.mark_pending {n : ℕ} {st st' : RawState n} {z : Fin n} {T : FHTree n}
    (hT : ValidSubtree st (some z) T) (hm0 : st.mark z = 0) (hm1 : st'.mark z = 1)
    (hm_other : ∀ x ∈ T.nodes, x ≠ z → st'.mark x = st.mark x)
    (hunch : ∀ x ∈ T.nodes,
      st'.inHeap x = st.inHeap x ∧ st'.deg x = st.deg x ∧ st'.child x = st.child x ∧
      st'.key x = st.key x)
    (hptr : ∀ x ∈ forestNodes T.children,
      st'.par x = st.par x ∧ st'.left x = st.left x ∧ st'.right x = st.right x) :
    ValidSubtree st' none T := by
  induction hT with
  | @mk u cs hin hmark hdeg hchild hpar hprio hrank _ ih =>
    have hu_in : u ∈ (FHTree.node u cs).nodes := List.mem_cons_self
    have hu := hunch u hu_in
    have hc_desc : ∀ c ∈ cs, c.root ∈ forestNodes cs := fun c hc =>
      mem_forestNodes_iff.mpr ⟨c, hc, c.root_mem_nodes⟩
    have hmu' : st'.mark u ≤ 1 := by
      by_cases huz : u = z
      · subst huz; omega
      · rw [hm_other u hu_in huz]; exact hmark
    refine ⟨hu.1.trans_ne hin, hmu', hu.2.1.trans hdeg, ?_, ?_, ?_, ?_, ?_⟩
    · rcases hchild with ⟨rfl, hc0⟩ | ⟨h, tail, hcu, hcirc, hperm⟩
      · exact Or.inl ⟨rfl, hu.2.2.1.trans hc0⟩
      · refine Or.inr ⟨h, tail, hu.2.2.1.trans hcu, hcirc.frame fun x hx => ?_, hperm⟩
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp (hperm.subset hx)
        have hp := hptr c.root (hc_desc c hc)
        exact ⟨hp.2.1, hp.2.2⟩
    · intro c hc
      exact (hptr c.root (hc_desc c hc)).1.trans (hpar c hc)
    · intro c hc
      have hci : c.root ∈ (FHTree.node u cs).nodes := List.mem_cons_of_mem u (hc_desc c hc)
      rw [hu.2.2.2, (hunch c.root hci).2.2.2]
      exact hprio c hc
    · intro i hi
      have hmem : cs[i] ∈ cs := List.getElem_mem hi
      have hci : (cs[i]).root ∈ (FHTree.node u cs).nodes :=
        List.mem_cons_of_mem u (hc_desc cs[i] hmem)
      have hr := hrank i hi
      simp only [reduceCtorEq, ↓reduceIte, Nat.add_zero]
      rw [(hunch (cs[i]).root hci).2.1]
      by_cases hwz : (cs[i]).root = z
      · rw [hwz] at hr ⊢
        simp only [↓reduceIte] at hr
        omega
      · simp only [Option.some.injEq, hwz, ↓reduceIte, Nat.add_zero] at hr
        rw [hm_other (cs[i]).root hci hwz]
        exact hr
    · intro c hc
      exact ih c hc
        (fun x hx => hm_other x (List.mem_cons_of_mem u (mem_forestNodes_iff.mpr ⟨c, hc, hx⟩)))
        (fun x hx => hunch x (List.mem_cons_of_mem u (mem_forestNodes_iff.mpr ⟨c, hc, hx⟩)))
        (fun x hx => hptr x
          (mem_forestNodes_iff.mpr ⟨c, hc, c.nodes_eq ▸ List.mem_cons_of_mem c.root hx⟩))

/-! ## Full heap representation invariant and core consequences -/

/-- Full structural, key, counter, and root-list invariant relating `s : IndexedMinPQ.State n` to
`st : RawState n`. -/
def FibRawInv (n K_max : ℕ) (s : IndexedMinPQ.State n) (st : RawState n) : Prop :=
  ∃ ts : List (FHTree n),
    (∀ T ∈ ts, ValidRoot st none T) ∧
    (forestNodes ts).Nodup ∧
    (∀ v : Fin n, v ∈ forestNodes ts ↔ (s v).isSome) ∧
    (∀ v : Fin n, (st.inHeap v ≠ 0 ↔ (s v).isSome) ∧ st.inHeap v ≤ 1) ∧
    (∀ v : Fin n, ∀ k : ℕ, s v = some k → st.key v = k ∧ k ≤ K_max) ∧
    st.sz = (IndexedMinPQ.dom s).card ∧
    st.numRoots = ts.length ∧
    st.numMarked = markedCount st ∧
    (∀ d ≤ n, st.cons d = 0) ∧
    ((ts = [] ∧ st.minRoot = 0) ∨
      ∃ (m : Fin n) (rtail : List (Fin n)),
        st.minRoot = m.val + 1 ∧
        IsCircList st.left st.right (m :: rtail) ∧
        (m :: rtail).Perm (ts.map FHTree.root) ∧
        ∀ T ∈ ts, IndexedMinPQ.PrioLE (m, st.key m) (T.root, st.key T.root))

/-- Transient forest invariant during `decreaseKey v k` while cascading cuts propagate from
`pending`. -/
def CutInv (n K_max : ℕ) (s : IndexedMinPQ.State n) (st : RawState n) (v m : Fin n)
    (pending : Option (Fin n)) : Prop :=
  ∃ ts : List (FHTree n),
    (∀ T ∈ ts, ValidRoot st pending T) ∧
    (forestNodes ts).Nodup ∧
    (∀ x : Fin n, x ∈ forestNodes ts ↔ (s x).isSome) ∧
    (∀ x : Fin n, (st.inHeap x ≠ 0 ↔ (s x).isSome) ∧ st.inHeap x ≤ 1) ∧
    (∀ x : Fin n, ∀ kx : ℕ, s x = some kx → st.key x = kx ∧ kx ≤ K_max) ∧
    st.sz = (IndexedMinPQ.dom s).card ∧
    st.numRoots = ts.length ∧
    st.numMarked = markedCount st ∧
    (∀ d ≤ n, st.cons d = 0) ∧
    (∃ rtail : List (Fin n),
      st.minRoot = m.val + 1 ∧
      IsCircList st.left st.right (m :: rtail) ∧
      (m :: rtail).Perm (ts.map FHTree.root)) ∧
    (∃ T_v ∈ ts, T_v.root = v) ∧
    (∀ T ∈ ts, T.root ≠ v → IndexedMinPQ.PrioLE (m, st.key m) (T.root, st.key T.root))

/-- `FibRawInv` holds on the empty priority queue whenever `inHeap` and `cons[0..n]` are zeroed and
the four scalar counters are `0`. -/
theorem FibRawInv.empty {n K_max : ℕ} {st : RawState n}
    (hin : ∀ v : Fin n, st.inHeap v = 0)
    (hcons : ∀ d ≤ n, st.cons d = 0)
    (hmin : st.minRoot = 0) (hnr : st.numRoots = 0) (hnm : st.numMarked = 0) (hsz : st.sz = 0) :
    FibRawInv n K_max (IndexedMinPQ.empty n) st := by
  refine ⟨[], ?_, List.nodup_nil, ?_, ?_, ?_, ?_, hnr, ?_, hcons, Or.inl ⟨rfl, hmin⟩⟩
  · intro _ h; exact absurd h List.not_mem_nil
  · intro v
    simp only [forestNodes, List.not_mem_nil, IndexedMinPQ.empty, Option.isSome_none,
      Bool.false_eq_true]
  · intro v
    exact ⟨by
      simp only [hin v, ne_eq, not_true_eq_false, IndexedMinPQ.empty, Option.isSome_none,
        Bool.false_eq_true],
      by rw [hin v]; omega⟩
  · intro _ _ h; simp only [IndexedMinPQ.empty, reduceCtorEq] at h
  · simp only [hsz, IndexedMinPQ.dom_empty, Finset.card_empty]
  · have hm0 : markedCount st = 0 := by
      unfold markedCount markedSet
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro u _
      simp only [hin u, ne_eq, not_true_eq_false, false_and, not_false_eq_true]
    omega

/-- All scalar counters of a valid Fibonacci heap are bounded by `n`. -/
theorem FibRawInv.bounds {n K_max : ℕ} {s : IndexedMinPQ.State n} {st : RawState n}
    (h : FibRawInv n K_max s st) :
    st.sz ≤ n ∧ st.numRoots ≤ n ∧ st.numMarked ≤ n ∧ st.minRoot ≤ n := by
  obtain ⟨ts, _, hnd, _, _, _, hsz, hnr, hnm, _, hrl⟩ := h
  have hfn_le : (forestNodes ts).length ≤ n := by simpa using hnd.length_le_card
  have hts_le : ts.length ≤ n := (forestNodes_length_ge ts).trans hfn_le
  have hdom_le : (IndexedMinPQ.dom s).card ≤ n :=
    (Finset.card_le_univ _).trans (by simp only [Fintype.card_fin, le_rfl])
  have hm_le : markedCount st ≤ n := markedCount_le_n st
  have hmin_le : st.minRoot ≤ n := by
    rcases hrl with ⟨_, hm0⟩ | ⟨m, _, hm, _, _, _⟩
    · omega
    · have := m.isLt; omega
  exact ⟨by omega, by omega, by omega, hmin_le⟩

/-- Concrete state uniquely determines the represented `IndexedMinPQ.State n`. -/
theorem FibRawInv.unique {n K_max : ℕ} {s₁ s₂ : IndexedMinPQ.State n} {st : RawState n}
    (h₁ : FibRawInv n K_max s₁ st) (h₂ : FibRawInv n K_max s₂ st) : s₁ = s₂ := by
  obtain ⟨_, _, _, _, hin₁, hkeys₁, _, _, _, _, _⟩ := h₁
  obtain ⟨_, _, _, _, hin₂, hkeys₂, _, _, _, _, _⟩ := h₂
  funext v
  have hiff : (s₁ v).isSome ↔ (s₂ v).isSome := (hin₁ v).1.symm.trans (hin₂ v).1
  cases hs₁ : s₁ v with
  | none =>
    cases hs₂ : s₂ v with
    | none => rfl
    | some k₂ =>
      have hf : (Option.none : Option ℕ).isSome = true :=
        hs₁ ▸ hiff.mpr (by simp only [hs₂, Option.isSome_some])
      simp only [Option.isSome_none, Bool.false_eq_true] at hf
  | some k₁ =>
    cases hs₂ : s₂ v with
    | none =>
      have hf : (Option.none : Option ℕ).isSome = true :=
        hs₂ ▸ hiff.mp (by simp only [hs₁, Option.isSome_some])
      simp only [Option.isSome_none, Bool.false_eq_true] at hf
    | some k₂ =>
      have hk₁ := (hkeys₁ v k₁ hs₁).1
      have hk₂ := (hkeys₂ v k₂ hs₂).1
      rw [← hk₁, hk₂]

/-- When `st.minRoot = 0`, `dom s = ∅` and `IndexedMinPQ.findMin s = none`. -/
theorem FibRawInv.findMin_eq_none {n K_max : ℕ} {s : IndexedMinPQ.State n} {st : RawState n}
    (h : FibRawInv n K_max s st) (h0 : st.minRoot = 0) :
    IndexedMinPQ.dom s = ∅ ∧ IndexedMinPQ.findMin s = none := by
  obtain ⟨ts, _, _, hdom, _, _, _, _, _, _, hrl⟩ := h
  rcases hrl with ⟨rfl, _⟩ | ⟨m, _, hm, _, _, _⟩
  · have hemp : IndexedMinPQ.dom s = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro v
      rw [IndexedMinPQ.notMem_dom_iff]
      cases hsv : s v with
      | none => rfl
      | some _ =>
        have hv := (hdom v).mpr (by simp only [hsv, Option.isSome_some])
        exact absurd hv List.not_mem_nil
    exact ⟨hemp, IndexedMinPQ.findMin_eq_none_iff.mpr hemp⟩
  · omega

/-- When `st.minRoot = z.val + 1`, `IndexedMinPQ.findMin s = some (z, st.key z)`. -/
theorem FibRawInv.findMin_eq_some {n K_max : ℕ} {s : IndexedMinPQ.State n} {st : RawState n}
    (h : FibRawInv n K_max s st) {z : Fin n} (hz : st.minRoot = z.val + 1) :
    IndexedMinPQ.findMin s = some (z, st.key z) ∧ s z = some (st.key z) ∧ st.key z ≤ K_max := by
  obtain ⟨ts, hroots, _, hdom, _, hkeys, _, _, _, _, hrl⟩ := h
  rcases hrl with ⟨_, hm0⟩ | ⟨m, rtail, hm, _, hperm, hmin_le⟩
  · omega
  · have hmz : m = z := Fin.ext (by omega)
    subst hmz
    have hm_map : m ∈ ts.map FHTree.root := hperm.subset List.mem_cons_self
    obtain ⟨T_m, hTm, hm_root⟩ := List.mem_map.mp hm_map
    have hm_in_fn : m ∈ forestNodes ts :=
      mem_forestNodes_iff.mpr ⟨T_m, hTm, hm_root ▸ T_m.root_mem_nodes⟩
    have hm_some : (s m).isSome := (hdom m).mp hm_in_fn
    obtain ⟨km, hsm⟩ := Option.isSome_iff_exists.mp hm_some
    obtain ⟨hkey_m, hkm_le⟩ := hkeys m km hsm
    subst hkey_m
    refine ⟨IndexedMinPQ.findMin_eq_some_iff.mpr ⟨hsm, fun v kv hsv => ?_⟩, hsm, hkm_le⟩
    have hv_fn : v ∈ forestNodes ts := (hdom v).mpr (by simp only [hsv, Option.isSome_some])
    obtain ⟨T_v, hTv, hv_in_Tv⟩ := mem_forestNodes_iff.mp hv_fn
    have hkv_eq : st.key v = kv := (hkeys v kv hsv).1
    subst hkv_eq
    have hle1 : IndexedMinPQ.PrioLE (m, st.key m) (T_v.root, st.key T_v.root) := hmin_le T_v hTv
    have hle2 : IndexedMinPQ.PrioLE (T_v.root, st.key T_v.root) (v, st.key v) :=
      (hroots T_v hTv).1.prioLE_of_mem hv_in_Tv
    exact hle1.trans hle2

end Cslib.Algorithms.WordRAM.PriorityQueue.FibonacciHeap
