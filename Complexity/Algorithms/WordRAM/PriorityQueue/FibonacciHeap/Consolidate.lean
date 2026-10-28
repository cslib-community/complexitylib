/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.PriorityQueue.FibonacciHeap.BasicOps

/-!
# Degree-indexed root consolidation and `extractMin` for a Fibonacci heap

This file proves the correctness, memory-safety, and `O(log n)` amortized instruction bound of
`scatterRootCode` and `extractMinCode` [Fredman and Tarjan][FredmanTarjan1987]
[Cormen et al., Section 19.2][CLRS2009]:

* **Degree-table invariant (`SlotInv`):** Tracks the subset `slotTrees` of consolidated root trees
  currently stored in `cons[0..maxDeg]`, maintaining pairwise-distinct degrees, `maxDeg ≤
  2 * Nat.log 2 n + 1`, and zeroing of all unoccupied entries `cons[d]` (`d ≤ n`).
* **Root scattering (`scatterRootCode_exec`):** Repeatedly links equal-degree roots via
  `ValidRoot.link` under lexicographic `IndexedMinPQ.PrioLT` using internal potential
  `50 * slotTrees.length`,
  executing in `t + 50 * slotTrees'.length ≤ 63 + 50 * slotTrees.length` steps while framing all
  other live nodes.
* **Minimum extraction (`extractMinCode_exec`):** Removes `z = minRoot - 1` (agreeing with
  `IndexedMinPQ.findMin`), scatters `z`'s children and the `numRoots - 1` remaining roots into
  `cons`, and scans only `0 .. maxDeg` (`≤ 2 * Nat.log 2 n + 2` slots) to rebuild the root circular
  list and `minRootReg` while restoring `cons = 0` in `t + potential y ≤ 410 * (Nat.log 2 n + 1) +
  potential x` instructions.

## Main definitions

* `Cslib.Algorithms.WordRAM.PriorityQueue.FibonacciHeap.SlotInv`: consolidation-table invariant
  tracking distinct-degree root trees in `cons[0..maxDeg]`.

## Main results

* `Cslib.Algorithms.WordRAM.PriorityQueue.FibonacciHeap.scatterRootCode_exec`: amortized root
  scattering and equal-degree linking specification.
* `Cslib.Algorithms.WordRAM.PriorityQueue.FibonacciHeap.extractMinCode_exec`: `O(log n)` amortized
  `extractMin` specification.

## References

* [M. L. Fredman and R. E. Tarjan, *Fibonacci Heaps and Their Uses in Improved Network Optimization
  Algorithms*][FredmanTarjan1987]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Section 19.2][CLRS2009]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.PriorityQueue.FibonacciHeap

open Cslib.WordRAM
open Cslib.Algorithms.Lean
open scoped Cslib.WordRAM

/-! ## Framing and pure-`ℕ` degree bounds during consolidation -/

/-- Framing `ValidRoot st none T` across a state transition preserving node fields on `T.nodes` and
pointer fields on strict descendants `forestNodes T.children`. -/
theorem ValidRoot.frame_tree {n : ℕ} {st st' : RawState n} {T : FHTree n}
    (hT : ValidRoot st none T)
    (hnode : ∀ u ∈ T.nodes,
      st'.inHeap u = st.inHeap u ∧ st'.mark u = st.mark u ∧ st'.deg u = st.deg u ∧
      st'.child u = st.child u ∧ st'.key u = st.key u ∧ st'.par u = st.par u)
    (hlr : ∀ u ∈ forestNodes T.children,
      st'.left u = st.left u ∧ st'.right u = st.right u) :
    ValidRoot st' none T := by
  have hr := hnode T.root T.root_mem_nodes
  refine ⟨hT.1.frame
    (fun u hu =>
      let h := hnode u hu
      ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩)
    (fun u hu =>
      let h := hnode u (T.nodes_eq ▸ List.mem_cons_of_mem T.root hu)
      let hl := hlr u hu
      ⟨h.2.2.2.2.2, hl.1, hl.2, Iff.rfl⟩),
    hr.2.2.2.2.2.trans hT.2.1, hr.2.1.trans hT.2.2⟩

/-- Framing `ValidRoot st none T` when all seven vertex arrays agree on `T.nodes`. -/
theorem ValidRoot.frame_nodes {n : ℕ} {st st' : RawState n} {T : FHTree n}
    (hT : ValidRoot st none T)
    (h : ∀ u ∈ T.nodes,
      st'.inHeap u = st.inHeap u ∧ st'.mark u = st.mark u ∧ st'.deg u = st.deg u ∧
      st'.child u = st.child u ∧ st'.key u = st.key u ∧ st'.par u = st.par u ∧
      st'.left u = st.left u ∧ st'.right u = st.right u) :
    ValidRoot st' none T :=
  hT.frame_tree
    (fun u hu =>
      let hu' := h u hu
      ⟨hu'.1, hu'.2.1, hu'.2.2.1, hu'.2.2.2.1, hu'.2.2.2.2.1, hu'.2.2.2.2.2.1⟩)
    (fun u hu =>
      let hu' := h u (T.nodes_eq ▸ List.mem_cons_of_mem T.root hu)
      hu'.2.2.2.2.2.2)

/-- Every valid subtree `T` disjoint from at least one other handle `z : Fin n` satisfies both
`T.deg ≤ 2 * Nat.log 2 n + 1` and `T.deg + 2 ≤ n`. -/
theorem deg_bounds_of_extra {n : ℕ} {st : RawState n} {T : FHTree n} {z : Fin n}
    (hT : ValidSubtree st none T) (hnd : (z :: T.nodes).Nodup) :
    T.deg ≤ 2 * Nat.log 2 n + 1 ∧ T.deg + 2 ≤ n := by
  have hlen : 1 + T.size ≤ n := by
    have h : (z :: T.nodes).length ≤ n := by simpa using hnd.length_le_card
    simp only [List.length_cons] at h
    unfold FHTree.size
    omega
  have hfib : Nat.fib (T.deg + 2) ≤ T.size := hT.fib_le_size
  have hd_size : T.deg + 1 ≤ T.size := (deg_add_one_le_fib T.deg).trans hfib
  have hd_log : T.deg ≤ 2 * Nat.log 2 n + 1 :=
    (hT.deg_bounds (m := n) (by omega)).1
  exact ⟨hd_log, by omega⟩

private theorem nodup_eraseIdx {α : Type*} :
    ∀ {L : List α} (i : ℕ), L.Nodup → (L.eraseIdx i).Nodup
  | [], _, _ => List.nodup_nil
  | _ :: _, 0, h => (List.nodup_cons.mp h).2
  | a :: tl, i + 1, h => by
    obtain ⟨ha, htl⟩ := List.nodup_cons.mp h
    rw [List.eraseIdx_cons_succ, List.nodup_cons]
    refine ⟨?_, nodup_eraseIdx i htl⟩
    intro hm
    obtain ⟨j, hj, _, rfl⟩ := List.mem_eraseIdx_iff_getElem.mp hm
    exact ha (List.getElem_mem hj)

private theorem map_eraseIdx_eq {α β : Type*} (f : α → β) :
    ∀ (L : List α) (i : ℕ), (L.eraseIdx i).map f = (L.map f).eraseIdx i
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: tl, i + 1 => by
    simp only [List.eraseIdx_cons_succ, List.map_cons, map_eraseIdx_eq f tl i]

private theorem length_eraseIdx_add_one {α : Type*} :
    ∀ (L : List α) (i : ℕ), i < L.length → (L.eraseIdx i).length + 1 = L.length
  | [], _, hi => absurd hi (Nat.not_lt_zero _)
  | _ :: _, 0, _ => rfl
  | _ :: tl, i + 1, hi => by
    simp only [List.eraseIdx_cons_succ, List.length_cons]
    have := length_eraseIdx_add_one tl i (Nat.lt_of_succ_lt_succ hi)
    omega

/-! ## Consolidation table invariant `SlotInv` -/

/-- Invariant for the degree consolidation table `st.cons` holding `slotTrees` within
`0 .. maxDeg`. -/
def SlotInv (n : ℕ) (st : RawState n) (slotTrees : List (FHTree n)) (maxDeg : ℕ) : Prop :=
  (slotTrees.map FHTree.deg).Nodup ∧
  (∀ T ∈ slotTrees, ValidRoot st none T ∧ T.deg ≤ maxDeg) ∧
  (∀ T ∈ slotTrees, st.cons T.deg = T.root.val + 1) ∧
  (∀ d ≤ n, (∀ T ∈ slotTrees, T.deg ≠ d) → st.cons d = 0) ∧
  maxDeg ≤ 2 * Nat.log 2 n + 1 ∧
  (maxDeg = 0 ∨ maxDeg + 2 ≤ n)

/-- Initial empty consolidation table when `∀ d ≤ n, st.cons d = 0`. -/
theorem SlotInv.empty {n : ℕ} {st : RawState n} (hcons : ∀ d ≤ n, st.cons d = 0) :
    SlotInv n st [] 0 :=
  ⟨List.nodup_nil,
   fun _ h => absurd h List.not_mem_nil,
   fun _ h => absurd h List.not_mem_nil,
   fun d hd _ => hcons d hd,
   by omega, Or.inl rfl⟩

/-- Framing `SlotInv` across a transition preserving `cons` and `ValidRoot` on `slotTrees`. -/
theorem SlotInv.frame {n maxDeg : ℕ} {st st' : RawState n} {slotTrees : List (FHTree n)}
    (hs : SlotInv n st slotTrees maxDeg)
    (hcons : st'.cons = st.cons)
    (hvalid : ∀ T ∈ slotTrees, ValidRoot st' none T) :
    SlotInv n st' slotTrees maxDeg := by
  obtain ⟨hnd, htr, hhit, hemp, hmd1, hmd2⟩ := hs
  exact ⟨hnd,
    fun T hT => ⟨hvalid T hT, (htr T hT).2⟩,
    fun T hT => hcons ▸ hhit T hT,
    fun d hd hnone => hcons ▸ hemp d hd hnone,
    hmd1, hmd2⟩

/-- Lookup in `st.cons d` (`d ≤ n`): either `st.cons d = 0` and no tree in `slotTrees` has degree
`d`, or a unique index `i < slotTrees.length` has `(slotTrees[i]).deg = d` and
`st.cons d = (slotTrees[i]).root.val + 1`. -/
theorem SlotInv.lookup {n maxDeg : ℕ} {st : RawState n} {slotTrees : List (FHTree n)}
    (hs : SlotInv n st slotTrees maxDeg) {d : ℕ} (hd : d ≤ n) :
    (st.cons d = 0 ∧ ∀ T ∈ slotTrees, T.deg ≠ d) ∨
    ∃ (i : ℕ) (hi : i < slotTrees.length),
      (slotTrees[i]).deg = d ∧
      st.cons d = (slotTrees[i]).root.val + 1 ∧
      (slotTrees.eraseIdx i).length + 1 = slotTrees.length ∧
      (∀ R ∈ slotTrees.eraseIdx i, R.deg ≠ d) := by
  obtain ⟨hnd, _, hhit, hemp, _, _⟩ := hs
  by_cases hex : ∃ T ∈ slotTrees, T.deg = d
  · right
    obtain ⟨T, hT_mem, hT_deg⟩ := hex
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hT_mem
    refine ⟨i, hi, hT_deg, hT_deg ▸ hhit slotTrees[i] (List.getElem_mem hi),
      length_eraseIdx_add_one slotTrees i hi, ?_⟩
    intro R hR hR_deg
    obtain ⟨j, hj, hji, rfl⟩ := List.mem_eraseIdx_iff_getElem.mp hR
    have hget : (slotTrees.map FHTree.deg)[j]'(by simp only [List.length_map]; exact hj) =
        (slotTrees.map FHTree.deg)[i]'(by simp only [List.length_map]; exact hi) := by
      simp only [List.getElem_map, hR_deg, hT_deg]
    exact hji ((List.Nodup.getElem_inj_iff hnd).mp hget)
  · left
    have hnone : ∀ T ∈ slotTrees, T.deg ≠ d := fun T hT e => hex ⟨T, hT, e⟩
    exact ⟨hemp d hd hnone, hnone⟩

private theorem getElem_mem_eraseIdx_of_ne {α : Type*} :
    ∀ (L : List α) (i k : ℕ) (_hi : i < L.length) (hk : k < L.length),
      k ≠ i → L[k] ∈ L.eraseIdx i
  | [], _, _, _, hk, _ => absurd hk (Nat.not_lt_zero _)
  | _ :: _, 0, 0, _, _, hki => absurd rfl hki
  | _ :: _, 0, _ + 1, _, hk, _ => by
    simp only [List.eraseIdx_zero, List.getElem_cons_succ]
    exact List.getElem_mem (Nat.lt_of_succ_lt_succ hk)
  | _ :: _, _ + 1, 0, _, _, _ => by
    simp only [List.eraseIdx_cons_succ, List.getElem_cons_zero]
    exact List.mem_cons_self
  | a :: tl, i + 1, k + 1, hi, hk, hki => by
    simp only [List.eraseIdx_cons_succ, List.getElem_cons_succ]
    exact List.mem_cons_of_mem a
      (getElem_mem_eraseIdx_of_ne tl i k (Nat.lt_of_succ_lt_succ hi) (Nat.lt_of_succ_lt_succ hk)
        fun e => hki (congrArg Nat.succ e))

/-- Clearing slot `d = (slotTrees[i]).deg` (`d ≤ n`) removes `slotTrees[i]` from `SlotInv`. -/
theorem SlotInv.step_collision {n maxDeg : ℕ} {st st' : RawState n} {slotTrees : List (FHTree n)}
    (hs : SlotInv n st slotTrees maxDeg) {i d : ℕ} (hi : i < slotTrees.length)
    (hdeg_i : (slotTrees[i]).deg = d) (_hd : d ≤ n)
    (hno_other : ∀ R ∈ slotTrees.eraseIdx i, R.deg ≠ d)
    (hcons' : st'.cons = Function.update st.cons d 0)
    (hvalid' : ∀ R ∈ slotTrees.eraseIdx i, ValidRoot st' none R) :
    SlotInv n st' (slotTrees.eraseIdx i) maxDeg := by
  obtain ⟨hnd, htr, hhit, hemp, hmd1, hmd2⟩ := hs
  refine ⟨by rw [map_eraseIdx_eq]; exact nodup_eraseIdx i hnd, ?_, ?_, ?_, hmd1, hmd2⟩
  · intro R hR
    obtain ⟨j, hj, _, rfl⟩ := List.mem_eraseIdx_iff_getElem.mp hR
    exact ⟨hvalid' _ hR, (htr _ (List.getElem_mem hj)).2⟩
  · intro R hR
    obtain ⟨j, hj, _, hR_eq⟩ := List.mem_eraseIdx_iff_getElem.mp hR
    rw [hcons', Function.update_of_ne (hno_other R hR)]
    exact hR_eq ▸ hhit _ (List.getElem_mem hj)
  · intro d' hd' hnone'
    rw [hcons']
    by_cases hdd : d' = d
    · rw [hdd, Function.update_self]
    · rw [Function.update_of_ne hdd]
      refine hemp d' hd' fun T hT hTd' => ?_
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hT
      by_cases hki : k = i
      · subst hki; exact hdd (hTd'.symm.trans hdeg_i)
      · exact hnone' slotTrees[k] (getElem_mem_eraseIdx_of_ne slotTrees i k hi hk hki) hTd'

/-- Storing a consolidated tree `T_cur` of unoccupied degree `d` into `st.cons d` and updating
`maxDeg` to `max maxDeg d` inserts `T_cur` into `SlotInv`. -/
theorem SlotInv.insert_empty {n maxDeg : ℕ} {st : RawState n} {slotTrees : List (FHTree n)}
    (hs : SlotInv n st slotTrees maxDeg) {T_cur : FHTree n} {d : ℕ}
    (_hd_n : d + 2 ≤ n) (hd_log : d ≤ 2 * Nat.log 2 n + 1)
    (hT_deg : T_cur.deg = d)
    (hnone : ∀ R ∈ slotTrees, R.deg ≠ d)
    (hT_valid : ValidRoot st none T_cur) :
    SlotInv n { st with cons := Function.update st.cons d (T_cur.root.val + 1) }
      (T_cur :: slotTrees) (max maxDeg d) := by
  obtain ⟨hnd, htr, hhit, hemp, hmd1, _⟩ := hs
  let st' : RawState n := { st with cons := Function.update st.cons d (T_cur.root.val + 1) }
  have hv_all : ∀ R : FHTree n, ValidRoot st none R → ValidRoot st' none R := fun R hR =>
    hR.frame_nodes fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine ⟨?_, ?_, ?_, ?_, by omega, Or.inr (by omega)⟩
  · rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, hnd⟩
    intro hm
    obtain ⟨R, hR, hR_eq⟩ := List.mem_map.mp hm
    exact hnone R hR (hR_eq.trans hT_deg)
  · intro R hR
    rcases List.mem_cons.mp hR with rfl | hR_tl
    · exact ⟨hv_all R hT_valid, by omega⟩
    · exact ⟨hv_all R (htr R hR_tl).1, (htr R hR_tl).2.trans (Nat.le_max_left maxDeg d)⟩
  · intro R hR
    rcases List.mem_cons.mp hR with rfl | hR_tl
    · dsimp only [st']
      rw [hT_deg, Function.update_self]
    · dsimp only [st']
      rw [Function.update_of_ne (hnone R hR_tl)]
      exact hhit R hR_tl
  · intro d' hd' hnone'
    dsimp only [st']
    have hne_d : d' ≠ d := fun e => hnone' T_cur List.mem_cons_self (hT_deg.trans e.symm)
    rw [Function.update_of_ne hne_d]
    exact hemp d' hd' fun R hR => hnone' R (List.mem_cons_of_mem T_cur hR)

/-- Once every degree `< maxDeg + 1` has been cleared from `SlotInv`, `slotTrees = []` and all
entries `st.cons d` (`d ≤ n`) are `0`. -/
theorem SlotInv.done_of_cleared {n maxDeg : ℕ} {st : RawState n} {slotTrees : List (FHTree n)}
    (hs : SlotInv n st slotTrees maxDeg)
    (hcleared : ∀ d < maxDeg + 1, ∀ T ∈ slotTrees, T.deg ≠ d) :
    slotTrees = [] ∧ ∀ d ≤ n, st.cons d = 0 := by
  obtain ⟨_, htr, _, hemp, _, _⟩ := hs
  have hnil : slotTrees = [] := by
    cases slotTrees with
    | nil => rfl
    | cons T rest =>
      have hle : T.deg < maxDeg + 1 := Nat.lt_succ_of_le (htr T List.mem_cons_self).2
      exact absurd rfl (hcleared T.deg hle T List.mem_cons_self)
  subst hnil
  exact ⟨rfl, fun d hd => hemp d hd fun _ h => absurd h List.not_mem_nil⟩

/-! ## Root scattering (`scatterBody_exec` and `scatterRootCode_exec`) -/

theorem FHTree.eta {n : ℕ} (T : FHTree n) : FHTree.node T.root T.children = T := by
  cases T
  rfl

private abbrev scatterBody : Code .exact rFib :=
  ram_exact[
    s5 ← s3 - oneP;
    s0 ← consBase + curDReg;
    *s0 ← zeroP;
    s0 ← baseReg + s4;
    s1 ← *s0;
    s0 ← baseReg + s5;
    s2 ← *s0;
    ⟪prioLTFlag s5 s2 s4 s1 s6⟫;
    if zeroP < s6 then [
      s6 ← s4;
      s4 ← s5;
      s5 ← s6
    ] else [
      s0 ← zeroP
    ];
    s1 ← s4 + oneP;
    s0 ← parBase + s5;
    *s0 ← s1;
    s0 ← degBase + s4;
    s1 ← *s0;
    if s1 = zeroP then [
      s0 ← leftBase + s5;
      *s0 ← s5;
      s0 ← rightBase + s5;
      *s0 ← s5;
      s2 ← s5 + oneP;
      s0 ← childBase + s4;
      *s0 ← s2;
      s0 ← degBase + s4;
      *s0 ← oneP
    ] else [
      s0 ← childBase + s4;
      s6 ← *s0;
      s6 ← s6 - oneP;
      ⟪insertIntoNonEmptyList s6 s5⟫;
      s1 ← s1 + oneP;
      s0 ← degBase + s4;
      *s0 ← s1
    ];
    curDReg ← curDReg + oneP;
    s0 ← consBase + curDReg;
    s3 ← *s0
  ]

/-- Single collision step of `scatterRootCode`: clears `cons[curD]`, orders `T_cur` (`s4`) and
`T_slot` (`s5`) under `IndexedMinPQ.PrioLT`, links the loser as newest child of the winner via
`ValidRoot.link`,
advances `curD` to `curD + 1`, and decreases `slotTrees.length` by `1` in `≤ 43` steps. -/
private theorem scatterBody_exec {n base w maxDeg curD : ℕ} {a : Data rFib}
    {T_cur : FHTree n} {slotTrees : List (FHTree n)} {otherNodes : List (Fin n)} {z : Fin n}
    (hb : a.Bounded w) (hbr : BaseRegs n base a)
    (hz_mem : z ∈ otherNodes)
    (hnd : (T_cur.nodes ++ (forestNodes slotTrees ++ otherNodes)).Nodup)
    (hs : SlotInv n (RawState.ofData n base a) slotTrees maxDeg)
    (hT_cur : ValidRoot (RawState.ofData n base a) none T_cur)
    (hcur_deg : T_cur.deg = curD)
    (ha_s4 : a.regs s4 = T_cur.root.val)
    (ha_curD : a.regs curDReg = curD)
    (ha_maxD : a.regs maxDegReg = maxDeg)
    (ha_s3 : a.regs s3 = (RawState.ofData n base a).cons curD)
    (hcond : (Cond.lt zeroP s3).Holds a) :
    ∃ a' T_next slotTrees',
      ExecWithin w scatterBody a a' 43 ∧
      a'.Bounded w ∧ BaseRegs n base a' ∧
      Modifies (Block.mk base (space n)).footprint a.mem a'.mem ∧
      (∀ r : Fin rFib, r.val < 33 → a'.regs r = a.regs r) ∧
      a'.regs maxDegReg = maxDeg ∧
      slotTrees'.length + 1 = slotTrees.length ∧
      (T_next.nodes ++ forestNodes slotTrees').Perm (T_cur.nodes ++ forestNodes slotTrees) ∧
      (T_next.nodes ++ (forestNodes slotTrees' ++ otherNodes)).Nodup ∧
      SlotInv n (RawState.ofData n base a') slotTrees' maxDeg ∧
      ValidRoot (RawState.ofData n base a') none T_next ∧
      T_next.deg = curD + 1 ∧
      a'.regs s4 = T_next.root.val ∧
      a'.regs curDReg = curD + 1 ∧
      a'.regs s3 = (RawState.ofData n base a').cons (curD + 1) ∧
      (let st := RawState.ofData n base a
       let st' := RawState.ofData n base a'
       st'.key = st.key ∧ st'.mark = st.mark ∧ st'.inHeap = st.inHeap ∧
       st'.minRoot = st.minRoot ∧ st'.numRoots = st.numRoots ∧
       st'.numMarked = st.numMarked ∧ st'.sz = st.sz ∧
       ∀ u ∈ otherNodes,
         st'.par u = st.par u ∧ st'.child u = st.child u ∧
         st'.left u = st.left u ∧ st'.right u = st.right u ∧ st'.deg u = st.deg u) := by
  set st := RawState.ofData n base a with hst_def
  have hfit_stop := hbr.fits_stop hb
  have hfit_n1 : Fits w (n + 1) := hfit_stop.of_le (by simp only [space]; omega)
  have hz0 : a.regs zeroP = 0 := hbr.2.2.2.2.2.2.2.2.2.2.2.1
  have ho1 : a.regs oneP = 1 := hbr.2.2.2.2.2.2.2.2.2.2.2.2
  have hbb : a.regs baseReg = base := hbr.2.2.1
  have hpb : a.regs parBase = base + n := hbr.2.2.2.1
  have hcb : a.regs childBase = base + 2 * n := hbr.2.2.2.2.1
  have hlb : a.regs leftBase = base + 3 * n := hbr.2.2.2.2.2.1
  have hrb : a.regs rightBase = base + 4 * n := hbr.2.2.2.2.2.2.1
  have hdb : a.regs degBase = base + 5 * n := hbr.2.2.2.2.2.2.2.1
  have hconsb : a.regs consBase = base + 8 * n := hbr.2.2.2.2.2.2.2.2.2.2.1
  -- Degree bound `curD + 2 ≤ n` from `z ∈ otherNodes` disjoint from `T_cur.nodes`:
  have hnd_cur_rest := List.nodup_append.mp hnd
  have hz_in_ro : z ∈ forestNodes slotTrees ++ otherNodes := List.mem_append_right _ hz_mem
  have hz_not_cur : z ∉ T_cur.nodes := fun hm => hnd_cur_rest.2.2 z hm z hz_in_ro rfl
  have hdeg_bds := deg_bounds_of_extra hT_cur.1 (List.nodup_cons.mpr ⟨hz_not_cur, hnd_cur_rest.1⟩)
  rw [hcur_deg] at hdeg_bds
  have hd_le_n : curD ≤ n := by omega
  have hd1_le_n : curD + 1 ≤ n := by omega
  -- `0 < st.cons curD` extracts the colliding slot tree `T_slot = slotTrees[idx]`:
  have hcons_pos : 0 < st.cons curD := by
    rw [Cond.Holds, hz0, ha_s3] at hcond
    exact hcond
  rcases hs.lookup hd_le_n with ⟨hc0, _⟩ | ⟨idx, hidx, hslot_deg, hcons_eq, hlen_er, hno_other⟩
  · omega
  let T_slot := slotTrees[idx]
  let slotTrees' := slotTrees.eraseIdx idx
  have hT_slot : ValidRoot st none T_slot := (hs.2.1 T_slot (List.getElem_mem hidx)).1
  have hperm_er : (T_slot.nodes ++ forestNodes slotTrees').Perm (forestNodes slotTrees) :=
    forestNodes_eraseIdx_perm slotTrees idx hidx
  have hnd_er : (T_cur.nodes ++ ((T_slot.nodes ++ forestNodes slotTrees') ++ otherNodes)).Nodup :=
    ((hperm_er.append_right otherNodes).append_left T_cur.nodes).nodup_iff.mpr hnd
  have hnd_assoc :
      ((T_cur.nodes ++ T_slot.nodes) ++ (forestNodes slotTrees' ++ otherNodes)).Nodup := by
    simpa only [List.append_assoc] using hnd_er
  have hnd_pair : (T_cur.nodes ++ T_slot.nodes).Nodup := (List.nodup_append.mp hnd_assoc).1
  let u4 := T_cur.root
  let u5 := T_slot.root
  have hu4_lt := u4.isLt
  have hu5_lt := u5.isLt
  have hu4_ne_u5 : u4 ≠ u5 :=
    (List.nodup_append.mp hnd_pair).2.2 u4 T_cur.root_mem_nodes u5 T_slot.root_mem_nodes
  -- Step 1 (`a → a1`, 3 steps): `s5 ← s3 - oneP; s0 ← consBase + curDReg; *s0 ← zeroP`
  have ho_cons_d := owns_cons_addr (base := base) hd_le_n
  let a1 := ((a.set s5 u5.val).set s0 (base + 8 * n + curD)).write (base + 8 * n + curD) 0
  have e1_1 : ExecWithin w (.op (.exactBin .sub s5 s3 oneP)) a (a.set s5 u5.val) 1 := by
    simpa only [ha_s3, hcons_eq, ho1, Nat.add_sub_cancel] using
      execWithin_exactSub (x := a) (d := s5) (i := s3) (j := oneP)
        (by rw [ha_s3, hcons_eq, ho1]; omega)
        (by rw [ha_s3, hcons_eq, ho1]; exact hfit_n1.of_le (by omega))
  have e1_2 : ExecWithin w (.op (.exactBin .add s0 consBase curDReg)) (a.set s5 u5.val)
      ((a.set s5 u5.val).set s0 (base + 8 * n + curD)) 1 := by
    have hcb1 : (a.set s5 u5.val).regs consBase = base + 8 * n := hconsb
    have hcd1 : (a.set s5 u5.val).regs curDReg = curD := ha_curD
    simpa only [hcb1, hcd1] using
      execWithin_exactAdd (x := a.set s5 u5.val) (d := s0) (i := consBase) (j := curDReg)
        (by rw [hcb1, hcd1]; exact hfit_stop.of_le (by simp only [space]; omega))
  have e1_3 : ExecWithin (B := .exact) w (.op (.store s0 zeroP))
      ((a.set s5 u5.val).set s0 (base + 8 * n + curD)) a1 1 := by
    have hs0_1 : ((a.set s5 u5.val).set s0 (base + 8 * n + curD)).regs s0 =
        base + 8 * n + curD := by simp only [Data.set_regs, Function.update_self]
    have hz_1 : ((a.set s5 u5.val).set s0 (base + 8 * n + curD)).regs zeroP = 0 := hz0
    simpa only [hs0_1, hz_1] using
      (ExecWithin.store (B := .exact) (w := w)
        (x := (a.set s5 u5.val).set s0 (base + 8 * n + curD)) (a := s0) (s := zeroP))
  have hb1 : a1.Bounded w := e1_3.bounded (e1_2.bounded (e1_1.bounded hb))
  have hbr1 : BaseRegs n base a1 :=
    ((hbr.set_non_base (by decide) _).set_non_base (by decide) _).write_eq _ _
  have hmod1 : Modifies (Block.mk base (space n)).footprint a.mem a1.mem :=
    Modifies.write_of_owns ho_cons_d 0
  have hst1 : RawState.ofData n base a1 = { st with cons := Function.update st.cons curD 0 } := by
    simp only [a1, ofData_write_cons hd_le_n, ofData_set_scratch _ (by decide : 17 ≤ s0.val),
      ofData_set_scratch _ (by decide : 17 ≤ s5.val), ← hst_def]
  -- Step 2 (`a1 → a2`, 10 steps): load `key[s4]`, `key[s5]`, and run `prioLTFlag s5 s2 s4 s1 s6`
  let a2_pre := (((a1.set s0 (base + u4.val)).set s1 (st.key u4)).set s0
    (base + u5.val)).set s2 (st.key u5)
  have e2_1 : ExecWithin w (.op (.exactBin .add s0 baseReg s4)) a1
      (a1.set s0 (base + u4.val)) 1 := by
    have hb_1 : a1.regs baseReg = base := hbb
    have hs4_1 : a1.regs s4 = u4.val := ha_s4
    simpa only [hb_1, hs4_1] using
      execWithin_exactAdd (x := a1) (d := s0) (i := baseReg) (j := s4)
        (by rw [hb_1, hs4_1]; exact hfit_stop.of_le (by simp only [space]; omega))
  have e2_2 : ExecWithin (B := .exact) w (.op (.load s1 s0)) (a1.set s0 (base + u4.val))
      ((a1.set s0 (base + u4.val)).set s1 (st.key u4)) 1 := by
    have hm_u4 : a1.mem (base + u4.val) = st.key u4 := by
      have : (RawState.ofData n base a1).key u4 = st.key u4 := by rw [hst1]
      exact this
    simpa only [Data.set_mem, Data.set_regs, Function.update_self, hm_u4] using
      (ExecWithin.load (B := .exact) (w := w) (x := a1.set s0 (base + u4.val)) (d := s1) (a := s0))
  have e2_3 : ExecWithin w (.op (.exactBin .add s0 baseReg s5))
      ((a1.set s0 (base + u4.val)).set s1 (st.key u4))
      (((a1.set s0 (base + u4.val)).set s1 (st.key u4)).set s0 (base + u5.val)) 1 := by
    have hb_2 : ((a1.set s0 (base + u4.val)).set s1 (st.key u4)).regs baseReg = base := hbb
    have hs5_2 : ((a1.set s0 (base + u4.val)).set s1 (st.key u4)).regs s5 = u5.val := by
      simp only [a1, Data.set_regs, Data.write_regs,
        Function.update_of_ne (by decide : s5 ≠ s1), Function.update_of_ne (by decide : s5 ≠ s0),
        Function.update_self]
    simpa only [hb_2, hs5_2] using
      execWithin_exactAdd (x := (a1.set s0 (base + u4.val)).set s1 (st.key u4))
        (d := s0) (i := baseReg) (j := s5)
        (by rw [hb_2, hs5_2]; exact hfit_stop.of_le (by simp only [space]; omega))
  have e2_4 : ExecWithin (B := .exact) w (.op (.load s2 s0))
      (((a1.set s0 (base + u4.val)).set s1 (st.key u4)).set s0 (base + u5.val)) a2_pre 1 := by
    have hm_u5 : a1.mem (base + u5.val) = st.key u5 := by
      have : (RawState.ofData n base a1).key u5 = st.key u5 := by rw [hst1]
      exact this
    simpa only [a2_pre, Data.set_mem, Data.set_regs, Function.update_self, hm_u5] using
      (ExecWithin.load (B := .exact) (w := w)
        (x := ((a1.set s0 (base + u4.val)).set s1 (st.key u4)).set s0 (base + u5.val))
        (d := s2) (a := s0))
  have hb2_pre : a2_pre.Bounded w := e2_4.bounded (e2_3.bounded (e2_2.bounded (e2_1.bounded hb1)))
  have hbr2_pre : BaseRegs n base a2_pre :=
    (((hbr1.set_non_base (by decide) _).set_non_base (by decide) _).set_non_base
      (by decide) _).set_non_base (by decide) _
  have ha2_s4 : a2_pre.regs s4 = u4.val := ha_s4
  have ha2_s5 : a2_pre.regs s5 = u5.val := by
    simp only [a2_pre, a1, Data.set_regs, Data.write_regs,
      Function.update_of_ne (by decide : s5 ≠ s2), Function.update_of_ne (by decide : s5 ≠ s0),
      Function.update_of_ne (by decide : s5 ≠ s1), Function.update_self]
  have ha2_s1 : a2_pre.regs s1 = st.key u4 := by
    simp only [a2_pre, Data.set_regs, Function.update_of_ne (by decide : s1 ≠ s2),
      Function.update_of_ne (by decide : s1 ≠ s0), Function.update_self]
  have ha2_s2 : a2_pre.regs s2 = st.key u5 := by
    simp only [a2_pre, Data.set_regs, Function.update_self]
  have he_plt := prioLTFlag_exec (w := w) hbr2_pre s5 s2 s4 s1 s6
  dsimp only at he_plt
  rw [ha2_s2, ha2_s1, ha2_s5, ha2_s4] at he_plt
  let bflag := if IndexedMinPQ.PrioLT (u5, st.key u5) (u4, st.key u4) then 1 else 0
  let a2 := a2_pre.set s6 bflag
  have e2_5 : ExecWithin w (prioLTFlag s5 s2 s4 s1 s6) a2_pre a2 6 := he_plt
  have hb2 : a2.Bounded w := e2_5.bounded hb2_pre
  have hbr2 : BaseRegs n base a2 := hbr2_pre.set_non_base (by decide) bflag
  have hst2 : RawState.ofData n base a2 = RawState.ofData n base a1 := by
    simp only [a2, a2_pre, ofData_set_scratch _ (by decide : 17 ≤ s6.val),
      ofData_set_scratch _ (by decide : 17 ≤ s2.val),
      ofData_set_scratch _ (by decide : 17 ≤ s0.val),
      ofData_set_scratch _ (by decide : 17 ≤ s1.val)]
  -- Step 3 (`a2 → a3`, ≤ 4 steps): swap `(s4, s5)` if `PrioLT (u5, key u5) (u4, key u4)`
  have hswap_step : ∃ (T₁ T₂ : FHTree n) (a3 : Data rFib),
      ExecWithin (B := .exact) w
        (.branch (.lt zeroP s6)
          (.seq (.op (.copy s6 s4)) (.seq (.op (.copy s4 s5)) (.op (.copy s5 s6))))
          (.op (.copy s0 zeroP))) a2 a3 4 ∧
      a3.Bounded w ∧ BaseRegs n base a3 ∧ a3.mem = a1.mem ∧
      RawState.ofData n base a3 = RawState.ofData n base a1 ∧
      (∀ r : Fin rFib, r.val < 35 → a3.regs r = a.regs r) ∧
      ValidRoot st none T₁ ∧ ValidRoot st none T₂ ∧
      T₁.deg = curD ∧ T₂.deg = curD ∧
      IndexedMinPQ.PrioLT (T₁.root, st.key T₁.root) (T₂.root, st.key T₂.root) ∧
      (T₁.nodes ++ T₂.nodes).Perm (T_cur.nodes ++ T_slot.nodes) ∧
      a3.regs s4 = T₁.root.val ∧ a3.regs s5 = T₂.root.val := by
    have hz_a2 : a2.regs zeroP = 0 := hbr2.2.2.2.2.2.2.2.2.2.2.2.1
    have hs4_a2 : a2.regs s4 = u4.val := ha_s4
    have hs5_a2 : a2.regs s5 = u5.val := by
      simp only [a2, Data.set_regs, Function.update_of_ne (by decide : s5 ≠ s6), ha2_s5]
    have hlow_a2 : ∀ r : Fin rFib, r.val < 35 → a2.regs r = a.regs r := fun r hr => by
      have ne_of : ∀ q : Fin rFib, 35 ≤ q.val → r ≠ q := fun q hq e => by subst e; omega
      simp only [a2, a2_pre, a1, Data.set_regs, Data.write_regs,
        Function.update_of_ne (ne_of s6 (by decide)),
        Function.update_of_ne (ne_of s2 (by decide)),
        Function.update_of_ne (ne_of s0 (by decide)),
        Function.update_of_ne (ne_of s1 (by decide)),
        Function.update_of_ne (ne_of s5 (by decide))]
    by_cases hlt54 : IndexedMinPQ.PrioLT (u5, st.key u5) (u4, st.key u4)
    · have hc_sw : (Cond.lt zeroP s6).Holds a2 := by
        rw [Cond.Holds, hz_a2]
        simp only [a2, Data.set_regs, Function.update_self, bflag, hlt54, ↓reduceIte]
        exact Nat.zero_lt_one
      let a3 := ((a2.set s6 u4.val).set s4 u5.val).set s5 u4.val
      have c1 : ExecWithin (B := .exact) w (.op (.copy s6 s4)) a2 (a2.set s6 u4.val) 1 := by
        simpa only [hs4_a2] using
          (ExecWithin.copy (B := .exact) (w := w) (x := a2) (d := s6) (s := s4))
      have c2 : ExecWithin (B := .exact) w (.op (.copy s4 s5)) (a2.set s6 u4.val)
          ((a2.set s6 u4.val).set s4 u5.val) 1 := by
        have hs5_c : (a2.set s6 u4.val).regs s5 = u5.val := by
          simp only [Data.set_regs, Function.update_of_ne (by decide : s5 ≠ s6), hs5_a2]
        simpa only [hs5_c] using
          (ExecWithin.copy (B := .exact) (w := w) (x := a2.set s6 u4.val) (d := s4) (s := s5))
      have c3 : ExecWithin (B := .exact) w (.op (.copy s5 s6)) ((a2.set s6 u4.val).set s4 u5.val)
          a3 1 := by
        have hs6_c : ((a2.set s6 u4.val).set s4 u5.val).regs s6 = u4.val := by
          simp only [Data.set_regs, Function.update_of_ne (by decide : s6 ≠ s4),
            Function.update_self]
        simpa only [hs6_c] using
          (ExecWithin.copy (B := .exact) (w := w)
            (x := (a2.set s6 u4.val).set s4 u5.val) (d := s5) (s := s6))
      have he_sw : ExecWithin (B := .exact) w
          (.branch (.lt zeroP s6)
            (.seq (.op (.copy s6 s4)) (.seq (.op (.copy s4 s5)) (.op (.copy s5 s6))))
            (.op (.copy s0 zeroP))) a2 a3 4 :=
        ExecWithin.branch_pos hc_sw (c1.seq (c2.seq c3))
      refine ⟨T_slot, T_cur, a3, he_sw, he_sw.bounded hb2,
        ((hbr2.set_non_base (by decide) _).set_non_base (by decide) _).set_non_base (by decide) _,
        rfl, ?_, ?_, hT_slot, hT_cur, hslot_deg, hcur_deg, hlt54, List.perm_append_comm, ?_, ?_⟩
      · simp only [a3, ofData_set_scratch _ (by decide : 17 ≤ s5.val),
          ofData_set_scratch _ (by decide : 17 ≤ s4.val),
          ofData_set_scratch _ (by decide : 17 ≤ s6.val), hst2]
      · intro r hr
        have ne_of : ∀ q : Fin rFib, 35 ≤ q.val → r ≠ q := fun q hq e => by subst e; omega
        simp only [a3, Data.set_regs, Function.update_of_ne (ne_of s5 (by decide)),
          Function.update_of_ne (ne_of s4 (by decide)),
          Function.update_of_ne (ne_of s6 (by decide)), hlow_a2 r hr]
      · simp only [a3, Data.set_regs, Function.update_of_ne (by decide : s4 ≠ s5),
          Function.update_self, u5]
      · simp only [a3, Data.set_regs, Function.update_self, u4]
    · have hc_sw : ¬(Cond.lt zeroP s6).Holds a2 := by
        rw [Cond.Holds, hz_a2]
        simp only [a2, Data.set_regs, Function.update_self, bflag, hlt54, ↓reduceIte,
          lt_self_iff_false, not_false_eq_true]
      let a3 := a2.set s0 0
      have c0 : ExecWithin (B := .exact) w (.op (.copy s0 zeroP)) a2 a3 1 := by
        simpa only [hz_a2] using
          (ExecWithin.copy (B := .exact) (w := w) (x := a2) (d := s0) (s := zeroP))
      have he_sw : ExecWithin (B := .exact) w
          (.branch (.lt zeroP s6)
            (.seq (.op (.copy s6 s4)) (.seq (.op (.copy s4 s5)) (.op (.copy s5 s6))))
            (.op (.copy s0 zeroP))) a2 a3 4 :=
        (ExecWithin.branch_neg hc_sw c0).mono (by omega)
      have hlt45 : IndexedMinPQ.PrioLT (u4, st.key u4) (u5, st.key u5) :=
        (IndexedMinPQ.prioLT_or_prioLT_of_ne hu4_ne_u5 (st.key u4) (st.key u5)).resolve_right hlt54
      refine ⟨T_cur, T_slot, a3, he_sw, he_sw.bounded hb2, hbr2.set_non_base (by decide) 0,
        rfl, (ofData_set_scratch a2 (by decide : 17 ≤ s0.val) 0).trans hst2, ?_,
        hT_cur, hT_slot, hcur_deg, hslot_deg, hlt45, List.Perm.refl _, ?_, ?_⟩
      · intro r hr
        have hne : r ≠ s0 := fun e => by subst e; change 35 < 35 at hr; omega
        simp only [a3, Data.set_regs, Function.update_of_ne hne, hlow_a2 r hr]
      · simp only [a3, Data.set_regs, Function.update_of_ne (by decide : s4 ≠ s0), hs4_a2, u4]
      · simp only [a3, Data.set_regs, Function.update_of_ne (by decide : s5 ≠ s0), hs5_a2, u5]
  obtain ⟨T₁, T₂, a3, e3, hb3, hbr3, hmem3, hst3, ha3_low, hT₁, hT₂, hd₁, hd₂, hprio12,
    hperm12, ha3_s4, ha3_s5⟩ := hswap_step
  let w1 := T₁.root
  let w2 := T₂.root
  have hw1_lt := w1.isLt
  have hw2_lt := w2.isLt
  have hnd12 : (T₁.nodes ++ T₂.nodes).Nodup := hperm12.nodup_iff.mpr hnd_pair
  have hw1_ne_w2 : w1 ≠ w2 :=
    (List.nodup_append.mp hnd12).2.2 w1 T₁.root_mem_nodes w2 T₂.root_mem_nodes
  -- Step 4 (`a3 → a4`, 5 steps): `par[w2] ← w1 + 1` and `s1 ← deg[w1] = curD`
  have hdeg_w1 : st.deg w1 = curD := by
    cases hT₁.1 with
    | mk _ _ hdeg_eq _ _ _ _ _ => exact hdeg_eq.trans hd₁
  have ho_pw2 : (Block.mk base (space n)).Owns (base + n + w2.val) := by
    have h := owns_arr_addr (base := base) (k := 1) (by decide) hw2_lt
    rw [Nat.one_mul] at h
    exact h
  let a4 := ((((a3.set s1 (w1.val + 1)).set s0 (base + n + w2.val)).write
    (base + n + w2.val) (w1.val + 1)).set s0 (base + 5 * n + w1.val)).set s1 curD
  have e4_1 : ExecWithin w (.op (.exactBin .add s1 s4 oneP)) a3 (a3.set s1 (w1.val + 1)) 1 := by
    have ho_3 : a3.regs oneP = 1 := hbr3.2.2.2.2.2.2.2.2.2.2.2.2
    simpa only [ha3_s4, ho_3, w1] using
      execWithin_exactAdd (x := a3) (d := s1) (i := s4) (j := oneP)
        (by rw [ha3_s4, ho_3]; exact hfit_n1.of_le (by omega))
  have e4_2 : ExecWithin w (.op (.exactBin .add s0 parBase s5)) (a3.set s1 (w1.val + 1))
      ((a3.set s1 (w1.val + 1)).set s0 (base + n + w2.val)) 1 := by
    have hp_3 : (a3.set s1 (w1.val + 1)).regs parBase = base + n := hbr3.2.2.2.1
    have hs5_3 : (a3.set s1 (w1.val + 1)).regs s5 = w2.val := by
      simp only [Data.set_regs, Function.update_of_ne (by decide : s5 ≠ s1), ha3_s5, w2]
    simpa only [hp_3, hs5_3] using
      execWithin_exactAdd (x := a3.set s1 (w1.val + 1)) (d := s0) (i := parBase) (j := s5)
        (by rw [hp_3, hs5_3]; exact hfit_stop.of_le (by simp only [space]; omega))
  have e4_3 : ExecWithin (B := .exact) w (.op (.store s0 s1))
      ((a3.set s1 (w1.val + 1)).set s0 (base + n + w2.val))
      (((a3.set s1 (w1.val + 1)).set s0 (base + n + w2.val)).write
        (base + n + w2.val) (w1.val + 1)) 1 := by
    have hs0_3 : ((a3.set s1 (w1.val + 1)).set s0 (base + n + w2.val)).regs s0 =
        base + n + w2.val := by simp only [Data.set_regs, Function.update_self]
    have hs1_3 : ((a3.set s1 (w1.val + 1)).set s0 (base + n + w2.val)).regs s1 = w1.val + 1 := by
      simp only [Data.set_regs, Function.update_of_ne (by decide : s1 ≠ s0), Function.update_self]
    simpa only [hs0_3, hs1_3] using
      (ExecWithin.store (B := .exact) (w := w)
        (x := (a3.set s1 (w1.val + 1)).set s0 (base + n + w2.val)) (a := s0) (s := s1))
  have e4_4 : ExecWithin w (.op (.exactBin .add s0 degBase s4))
      (((a3.set s1 (w1.val + 1)).set s0 (base + n + w2.val)).write
        (base + n + w2.val) (w1.val + 1))
      ((((a3.set s1 (w1.val + 1)).set s0 (base + n + w2.val)).write
        (base + n + w2.val) (w1.val + 1)).set s0 (base + 5 * n + w1.val)) 1 := by
    have hd_3 : (((a3.set s1 (w1.val + 1)).set s0 (base + n + w2.val)).write
        (base + n + w2.val) (w1.val + 1)).regs degBase = base + 5 * n := hbr3.2.2.2.2.2.2.2.1
    have hs4_3 : (((a3.set s1 (w1.val + 1)).set s0 (base + n + w2.val)).write
        (base + n + w2.val) (w1.val + 1)).regs s4 = w1.val := by
      simp only [Data.write_regs, Data.set_regs, Function.update_of_ne (by decide : s4 ≠ s0),
        Function.update_of_ne (by decide : s4 ≠ s1), ha3_s4, w1]
    simpa only [hd_3, hs4_3] using
      execWithin_exactAdd
        (x := ((a3.set s1 (w1.val + 1)).set s0 (base + n + w2.val)).write
          (base + n + w2.val) (w1.val + 1))
        (d := s0) (i := degBase) (j := s4)
        (by rw [hd_3, hs4_3]; exact hfit_stop.of_le (by simp only [space]; omega))
  have hst4_pre : RawState.ofData n base
      ((((a3.set s1 (w1.val + 1)).set s0 (base + n + w2.val)).write
        (base + n + w2.val) (w1.val + 1)).set s0 (base + 5 * n + w1.val)) =
      { st with
        par := Function.update st.par w2 (w1.val + 1)
        cons := Function.update st.cons curD 0 } := by
    simp only [ofData_set_scratch _ (by decide : 17 ≤ s0.val), ofData_write_par,
      ofData_set_scratch _ (by decide : 17 ≤ s1.val), hst3, hst1]
  have e4_5 : ExecWithin (B := .exact) w (.op (.load s1 s0))
      ((((a3.set s1 (w1.val + 1)).set s0 (base + n + w2.val)).write
        (base + n + w2.val) (w1.val + 1)).set s0 (base + 5 * n + w1.val)) a4 1 := by
    have hm_dw1 : (((a3.set s1 (w1.val + 1)).set s0 (base + n + w2.val)).write
        (base + n + w2.val) (w1.val + 1)).mem (base + 5 * n + w1.val) = curD := by
      have : (RawState.ofData n base
          ((((a3.set s1 (w1.val + 1)).set s0 (base + n + w2.val)).write
            (base + n + w2.val) (w1.val + 1)).set s0 (base + 5 * n + w1.val))).deg w1 = curD := by
        rw [hst4_pre]; exact hdeg_w1
      exact this
    simpa only [a4, Data.set_mem, Data.set_regs, Function.update_self, hm_dw1] using
      (ExecWithin.load (B := .exact) (w := w)
        (x := (((a3.set s1 (w1.val + 1)).set s0 (base + n + w2.val)).write
          (base + n + w2.val) (w1.val + 1)).set s0 (base + 5 * n + w1.val))
        (d := s1) (a := s0))
  have hb4 : a4.Bounded w :=
    e4_5.bounded (e4_4.bounded (e4_3.bounded (e4_2.bounded (e4_1.bounded hb3))))
  have hbr4 : BaseRegs n base a4 :=
    ((((hbr3.set_non_base (by decide) _).set_non_base (by decide) _).write_eq _ _).set_non_base
      (by decide) _).set_non_base (by decide) _
  have hmod4 : Modifies (Block.mk base (space n)).footprint a.mem a4.mem := by
    have hm34 : Modifies (Block.mk base (space n)).footprint a1.mem a4.mem := by
      change Modifies (Block.mk base (space n)).footprint a1.mem
        (Function.update a3.mem (base + n + w2.val) (w1.val + 1))
      rw [hmem3]
      exact Modifies.write_of_owns ho_pw2 (w1.val + 1)
    exact modifies_block_trans hmod1 hm34
  have hst4 : RawState.ofData n base a4 =
      { st with
        par := Function.update st.par w2 (w1.val + 1)
        cons := Function.update st.cons curD 0 } :=
    (ofData_set_scratch _ (by decide : 17 ≤ s1.val) curD).trans hst4_pre
  have ha4_low : ∀ r : Fin rFib, r.val < 35 → a4.regs r = a.regs r := fun r hr => by
    have ne0 : r ≠ s0 := fun e => by subst e; change 35 < 35 at hr; omega
    have ne1 : r ≠ s1 := fun e => by subst e; change 36 < 35 at hr; omega
    simp only [a4, Data.set_regs, Data.write_regs, Function.update_of_ne ne1,
      Function.update_of_ne ne0, ha3_low r hr]
  have ha4_s4 : a4.regs s4 = w1.val := by
    simp only [a4, Data.set_regs, Data.write_regs, Function.update_of_ne (by decide : s4 ≠ s1),
      Function.update_of_ne (by decide : s4 ≠ s0), ha3_s4, w1]
  have ha4_s5 : a4.regs s5 = w2.val := by
    simp only [a4, Data.set_regs, Data.write_regs, Function.update_of_ne (by decide : s5 ≠ s1),
      Function.update_of_ne (by decide : s5 ≠ s0), ha3_s5, w2]
  have ha4_s1 : a4.regs s1 = curD := by
    simp only [a4, Data.set_regs, Function.update_self]
  -- Step 5 (`a4 → a5`, ≤ 18 steps): splice `w2` into `w1`'s child list and increment `deg[w1]`
  let T_next : FHTree n := FHTree.node w1 (T₁.children ++ [T₂])
  have hT_next_nodes : T_next.nodes = T₁.nodes ++ T₂.nodes := by
    simp only [T_next, w1, link_nodes_eq, FHTree.eta]
  let cStep5 : Code .exact rFib :=
    ram_exact[
      if s1 = zeroP then [
        s0 ← leftBase + s5;
        *s0 ← s5;
        s0 ← rightBase + s5;
        *s0 ← s5;
        s2 ← s5 + oneP;
        s0 ← childBase + s4;
        *s0 ← s2;
        s0 ← degBase + s4;
        *s0 ← oneP
      ] else [
        s0 ← childBase + s4;
        s6 ← *s0;
        s6 ← s6 - oneP;
        ⟪insertIntoNonEmptyList s6 s5⟫;
        s1 ← s1 + oneP;
        s0 ← degBase + s4;
        *s0 ← s1
      ]
    ]
  have hstep5 : ∃ a5,
      ExecWithin w cStep5 a4 a5 18 ∧
      a5.Bounded w ∧ BaseRegs n base a5 ∧
      Modifies (Block.mk base (space n)).footprint a4.mem a5.mem ∧
      (∀ r : Fin rFib, r.val < 35 → a5.regs r = a.regs r) ∧
      a5.regs s4 = w1.val ∧
      ValidRoot (RawState.ofData n base a5) none T_next ∧
      (let st5 := RawState.ofData n base a5
       st5.key = st.key ∧ st5.mark = st.mark ∧ st5.inHeap = st.inHeap ∧
       st5.cons = Function.update st.cons curD 0 ∧
       st5.minRoot = st.minRoot ∧ st5.numRoots = st.numRoots ∧
       st5.numMarked = st.numMarked ∧ st5.sz = st.sz ∧
       ∀ u, u ∉ T₁.nodes ++ T₂.nodes →
         st5.par u = st.par u ∧ st5.child u = st.child u ∧
         st5.left u = st.left u ∧ st5.right u = st.right u ∧ st5.deg u = st.deg u) := by
    have hz_4 : a4.regs zeroP = 0 := hbr4.2.2.2.2.2.2.2.2.2.2.2.1
    have ho_4 : a4.regs oneP = 1 := hbr4.2.2.2.2.2.2.2.2.2.2.2.2
    have hcb_4 : a4.regs childBase = base + 2 * n := hbr4.2.2.2.2.1
    have hlb_4 : a4.regs leftBase = base + 3 * n := hbr4.2.2.2.2.2.1
    have hrb_4 : a4.regs rightBase = base + 4 * n := hbr4.2.2.2.2.2.2.1
    have hdb_4 : a4.regs degBase = base + 5 * n := hbr4.2.2.2.2.2.2.2.1
    have ho_cw1 := owns_arr_addr (base := base) (k := 2) (by decide) hw1_lt
    have ho_dw1 := owns_arr_addr (base := base) (k := 5) (by decide) hw1_lt
    by_cases hd0 : curD = 0
    · have hc5 : (Cond.eq s1 zeroP).Holds a4 := by simp only [Cond.Holds, ha4_s1, hz_4, hd0]
      have ho_lw2 := owns_arr_addr (base := base) (k := 3) (by decide) hw2_lt
      have ho_rw2 := owns_arr_addr (base := base) (k := 4) (by decide) hw2_lt
      let p1 := (a4.set s0 (base + 3 * n + w2.val)).write (base + 3 * n + w2.val) w2.val
      let p2 := (p1.set s0 (base + 4 * n + w2.val)).write (base + 4 * n + w2.val) w2.val
      let p3 := ((p2.set s2 (w2.val + 1)).set s0 (base + 2 * n + w1.val)).write
        (base + 2 * n + w1.val) (w2.val + 1)
      let a5 := (p3.set s0 (base + 5 * n + w1.val)).write (base + 5 * n + w1.val) 1
      have s1_a : ExecWithin w (.op (.exactBin .add s0 leftBase s5)) a4
          (a4.set s0 (base + 3 * n + w2.val)) 1 := by
        simpa only [hlb_4, ha4_s5] using
          execWithin_exactAdd (x := a4) (d := s0) (i := leftBase) (j := s5)
            (by rw [hlb_4, ha4_s5]; exact hfit_stop.of_le (by simp only [space]; omega))
      have s1_b : ExecWithin (B := .exact) w (.op (.store s0 s5))
          (a4.set s0 (base + 3 * n + w2.val)) p1 1 := by
        simpa only [Data.set_regs, Function.update_self,
          Function.update_of_ne (by decide : s5 ≠ s0), ha4_s5] using
          (ExecWithin.store (B := .exact) (w := w) (x := a4.set s0 (base + 3 * n + w2.val))
            (a := s0) (s := s5))
      have s2_a : ExecWithin w (.op (.exactBin .add s0 rightBase s5)) p1
          (p1.set s0 (base + 4 * n + w2.val)) 1 := by
        have hr_p1 : p1.regs rightBase = base + 4 * n := hrb_4
        have hs5_p1 : p1.regs s5 = w2.val := by
          simp only [p1, Data.write_regs, Data.set_regs,
            Function.update_of_ne (by decide : s5 ≠ s0), ha4_s5]
        simpa only [hr_p1, hs5_p1] using
          execWithin_exactAdd (x := p1) (d := s0) (i := rightBase) (j := s5)
            (by rw [hr_p1, hs5_p1]; exact hfit_stop.of_le (by simp only [space]; omega))
      have s2_b : ExecWithin (B := .exact) w (.op (.store s0 s5))
          (p1.set s0 (base + 4 * n + w2.val)) p2 1 := by
        have hs5_p1 : (p1.set s0 (base + 4 * n + w2.val)).regs s5 = w2.val := by
          simp only [p1, Data.write_regs, Data.set_regs,
            Function.update_of_ne (by decide : s5 ≠ s0), ha4_s5]
        simpa only [Data.set_regs, Function.update_self, hs5_p1] using
          (ExecWithin.store (B := .exact) (w := w) (x := p1.set s0 (base + 4 * n + w2.val))
            (a := s0) (s := s5))
      have s3_a : ExecWithin w (.op (.exactBin .add s2 s5 oneP)) p2 (p2.set s2 (w2.val + 1)) 1 := by
        have hs5_p2 : p2.regs s5 = w2.val := by
          simp only [p2, p1, Data.write_regs, Data.set_regs,
            Function.update_of_ne (by decide : s5 ≠ s0), ha4_s5]
        have ho_p2 : p2.regs oneP = 1 := ho_4
        simpa only [hs5_p2, ho_p2] using
          execWithin_exactAdd (x := p2) (d := s2) (i := s5) (j := oneP)
            (by rw [hs5_p2, ho_p2]; exact hfit_n1.of_le (by omega))
      have s3_b : ExecWithin w (.op (.exactBin .add s0 childBase s4)) (p2.set s2 (w2.val + 1))
          ((p2.set s2 (w2.val + 1)).set s0 (base + 2 * n + w1.val)) 1 := by
        have hc_p2 : (p2.set s2 (w2.val + 1)).regs childBase = base + 2 * n := hcb_4
        have hs4_p2 : (p2.set s2 (w2.val + 1)).regs s4 = w1.val := by
          simp only [p2, p1, Data.write_regs, Data.set_regs,
            Function.update_of_ne (by decide : s4 ≠ s2),
            Function.update_of_ne (by decide : s4 ≠ s0), ha4_s4]
        simpa only [hc_p2, hs4_p2] using
          execWithin_exactAdd (x := p2.set s2 (w2.val + 1)) (d := s0) (i := childBase) (j := s4)
            (by rw [hc_p2, hs4_p2]; exact hfit_stop.of_le (by simp only [space]; omega))
      have s3_c : ExecWithin (B := .exact) w (.op (.store s0 s2))
          ((p2.set s2 (w2.val + 1)).set s0 (base + 2 * n + w1.val)) p3 1 := by
        have hs2_p2 : ((p2.set s2 (w2.val + 1)).set s0 (base + 2 * n + w1.val)).regs s2 =
            w2.val + 1 := by
          simp only [Data.set_regs, Function.update_of_ne (by decide : s2 ≠ s0),
            Function.update_self]
        simpa only [Data.set_regs, Function.update_self, hs2_p2] using
          (ExecWithin.store (B := .exact) (w := w)
            (x := (p2.set s2 (w2.val + 1)).set s0 (base + 2 * n + w1.val)) (a := s0) (s := s2))
      have s4_a : ExecWithin w (.op (.exactBin .add s0 degBase s4)) p3
          (p3.set s0 (base + 5 * n + w1.val)) 1 := by
        have hd_p3 : p3.regs degBase = base + 5 * n := hdb_4
        have hs4_p3 : p3.regs s4 = w1.val := by
          simp only [p3, p2, p1, Data.write_regs, Data.set_regs,
            Function.update_of_ne (by decide : s4 ≠ s0),
            Function.update_of_ne (by decide : s4 ≠ s2), ha4_s4]
        simpa only [hd_p3, hs4_p3] using
          execWithin_exactAdd (x := p3) (d := s0) (i := degBase) (j := s4)
            (by rw [hd_p3, hs4_p3]; exact hfit_stop.of_le (by simp only [space]; omega))
      have s4_b : ExecWithin (B := .exact) w (.op (.store s0 oneP))
          (p3.set s0 (base + 5 * n + w1.val)) a5 1 := by
        have ho_p3 : (p3.set s0 (base + 5 * n + w1.val)).regs oneP = 1 := ho_4
        simpa only [Data.set_regs, Function.update_self, ho_p3] using
          (ExecWithin.store (B := .exact) (w := w)
            (x := p3.set s0 (base + 5 * n + w1.val)) (a := s0) (s := oneP))
      have he_pos := s1_a.seq <| s1_b.seq <| s2_a.seq <| s2_b.seq <| s3_a.seq <|
        s3_b.seq <| s3_c.seq <| s4_a.seq s4_b
      have he5 : ExecWithin w cStep5 a4 a5 18 :=
        (ExecWithin.branch_pos hc5 he_pos).mono (by omega)
      have hbr5 : BaseRegs n base a5 :=
        ((((((((hbr4.set_non_base (by decide) _).write_eq _ _).set_non_base
          (by decide) _).write_eq _ _).set_non_base (by decide) _).set_non_base
          (by decide) _).write_eq _ _).set_non_base (by decide) _).write_eq _ _
      have hmod5 : Modifies (Block.mk base (space n)).footprint a4.mem a5.mem :=
        modifies_block_trans (Modifies.write_of_owns ho_lw2 w2.val) <|
        modifies_block_trans (Modifies.write_of_owns ho_rw2 w2.val) <|
        modifies_block_trans (Modifies.write_of_owns ho_cw1 (w2.val + 1))
          (Modifies.write_of_owns ho_dw1 1)
      have hst5 : RawState.ofData n base a5 =
          { st with
            par := Function.update st.par w2 (w1.val + 1)
            child := Function.update st.child w1 (w2.val + 1)
            left := Function.update st.left w2 w2.val
            right := Function.update st.right w2 w2.val
            deg := Function.update st.deg w1 1
            cons := Function.update st.cons curD 0 } := by
        simp only [a5, p3, p2, p1, ofData_write_deg, ofData_write_child, ofData_write_right,
          ofData_write_left, ofData_set_scratch _ (by decide : 17 ≤ s0.val),
          ofData_set_scratch _ (by decide : 17 ≤ s2.val), hst4]
      have hcs1_nil : T₁.children = [] := List.eq_nil_of_length_eq_zero (hd₁.trans hd0)
      have hvalid5 : ValidRoot (RawState.ofData n base a5) none T_next := by
        rw [hst5]
        dsimp only [w1, w2]
        refine hT₁.link hT₂ hnd12 (hd₁.trans hd₂.symm) hprio12
          (fun _ _ => ⟨rfl, rfl, rfl⟩)
          ⟨by dsimp only; rw [hd₁, hd0, Function.update_self],
           fun x _ hx => Function.update_of_ne hx _ _⟩
          ⟨by dsimp only; rw [Function.update_of_ne hw1_ne_w2]; exact hT₁.2.1,
           Function.update_self _ _ _,
           fun x _ hx => Function.update_of_ne hx _ _⟩
          ⟨⟨w2, [], Function.update_self _ _ _, IsCircList.singleton st.left st.right w2,
            by simp only [hcs1_nil, List.nil_append, List.map_singleton, w2, List.Perm.refl]⟩,
           fun x _ hx => Function.update_of_ne hx _ _⟩
          (fun x _ hxw2 _ => ⟨Function.update_of_ne hxw2 _ _, Function.update_of_ne hxw2 _ _⟩)
      refine ⟨a5, he5, he5.bounded hb4, hbr5, hmod5, ?_, ?_, hvalid5, ?_⟩
      · intro r hr
        have ne0 : r ≠ s0 := fun e => by subst e; change 35 < 35 at hr; omega
        have ne2 : r ≠ s2 := fun e => by subst e; change 37 < 35 at hr; omega
        simp only [a5, p3, p2, p1, Data.write_regs, Data.set_regs,
          Function.update_of_ne ne0, Function.update_of_ne ne2, ha4_low r hr]
      · simp only [a5, p3, p2, p1, Data.write_regs, Data.set_regs,
          Function.update_of_ne (by decide : s4 ≠ s0),
          Function.update_of_ne (by decide : s4 ≠ s2), ha4_s4, w1]
      · dsimp only
        rw [hst5]
        refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun u hu => ?_⟩
        have hu1 : u ≠ w1 := fun e => hu (List.mem_append_left _ (e ▸ T₁.root_mem_nodes))
        have hu2 : u ≠ w2 := fun e => hu (List.mem_append_right _ (e ▸ T₂.root_mem_nodes))
        exact ⟨Function.update_of_ne hu2 _ _, Function.update_of_ne hu1 _ _,
          Function.update_of_ne hu2 _ _, Function.update_of_ne hu2 _ _,
          Function.update_of_ne hu1 _ _⟩
    · have hc5 : ¬(Cond.eq s1 zeroP).Holds a4 := by
        simp only [Cond.Holds, ha4_s1, hz_4, hd0, not_false_eq_true]
      -- Extract `T₁`'s non-empty child circular list `h :: tail`
      have hchild1 : ∃ (h : Fin n) (tail : List (Fin n)),
          st.child w1 = h.val + 1 ∧ IsCircList st.left st.right (h :: tail) ∧
          (h :: tail).Perm (T₁.children.map FHTree.root) := by
        change ∃ (h : Fin n) (tail : List (Fin n)),
          st.child T₁.root = h.val + 1 ∧ IsCircList st.left st.right (h :: tail) ∧
          (h :: tail).Perm (T₁.children.map FHTree.root)
        rcases hT₁ with ⟨⟨_, _, _, hch, _, _, _, _⟩, _⟩
        rcases hch with ⟨rfl, _⟩ | hsome
        · simp only [FHTree.deg_node, List.length_nil] at hd₁
          exact absurd hd₁.symm hd0
        · simpa only [FHTree.root_node, FHTree.children_node] using hsome
      obtain ⟨h_c, tail_c, hcw1_eq, hcirc_c, hperm_c⟩ := hchild1
      have hhc_lt := h_c.isLt
      let q1 := ((a4.set s0 (base + 2 * n + w1.val)).set s6 (h_c.val + 1)).set s6 h_c.val
      have t1 : ExecWithin w (.op (.exactBin .add s0 childBase s4)) a4
          (a4.set s0 (base + 2 * n + w1.val)) 1 := by
        simpa only [hcb_4, ha4_s4] using
          execWithin_exactAdd (x := a4) (d := s0) (i := childBase) (j := s4)
            (by rw [hcb_4, ha4_s4]; exact hfit_stop.of_le (by simp only [space]; omega))
      have t2 : ExecWithin (B := .exact) w (.op (.load s6 s0)) (a4.set s0 (base + 2 * n + w1.val))
          ((a4.set s0 (base + 2 * n + w1.val)).set s6 (h_c.val + 1)) 1 := by
        have hm_cw1 : a4.mem (base + 2 * n + w1.val) = h_c.val + 1 := by
          have : (RawState.ofData n base a4).child w1 = h_c.val + 1 := by rw [hst4]; exact hcw1_eq
          exact this
        simpa only [Data.set_mem, Data.set_regs, Function.update_self, hm_cw1] using
          (ExecWithin.load (B := .exact) (w := w) (x := a4.set s0 (base + 2 * n + w1.val))
            (d := s6) (a := s0))
      have t3 : ExecWithin w (.op (.exactBin .sub s6 s6 oneP))
          ((a4.set s0 (base + 2 * n + w1.val)).set s6 (h_c.val + 1)) q1 1 := by
        have hs6_q : ((a4.set s0 (base + 2 * n + w1.val)).set s6 (h_c.val + 1)).regs s6 =
            h_c.val + 1 := by simp only [Data.set_regs, Function.update_self]
        have ho_q : ((a4.set s0 (base + 2 * n + w1.val)).set s6 (h_c.val + 1)).regs oneP = 1 :=
          ho_4
        simpa only [hs6_q, ho_q, Nat.add_sub_cancel] using
          execWithin_exactSub
            (x := (a4.set s0 (base + 2 * n + w1.val)).set s6 (h_c.val + 1))
            (d := s6) (i := s6) (j := oneP)
            (by rw [hs6_q, ho_q]; omega)
            (by rw [hs6_q, ho_q]; exact hfit_n1.of_le (by omega))
      have hb_q1 : q1.Bounded w := t3.bounded (t2.bounded (t1.bounded hb4))
      have hbr_q1 : BaseRegs n base q1 :=
        ((hbr4.set_non_base (by decide) _).set_non_base (by decide) _).set_non_base (by decide) _
      have hst_q1 : RawState.ofData n base q1 = RawState.ofData n base a4 := by
        simp only [q1, ofData_set_scratch _ (by decide : 17 ≤ s6.val),
          ofData_set_scratch _ (by decide : 17 ≤ s0.val)]
      have hq1_s6 : q1.regs s6 = h_c.val := by simp only [q1, Data.set_regs, Function.update_self]
      have hq1_s5 : q1.regs s5 = w2.val := by
        simp only [q1, Data.set_regs, Function.update_of_ne (by decide : s5 ≠ s6),
          Function.update_of_ne (by decide : s5 ≠ s0), ha4_s5]
      have hw2_not_ht : w2 ∉ h_c :: tail_c := by
        intro hm_in
        obtain ⟨c, hc, hcr⟩ := List.mem_map.mp (hperm_c.subset hm_in)
        have hw2_in_1 : w2 ∈ T₁.nodes :=
          T₁.nodes_eq ▸ List.mem_cons_of_mem w1
            (mem_forestNodes_iff.mpr ⟨c, hc, hcr ▸ c.root_mem_nodes⟩)
        exact (List.nodup_append.mp hnd12).2.2 w2 hw2_in_1 w2 T₂.root_mem_nodes rfl
      have hcirc_q1 : IsCircList (RawState.ofData n base q1).left
          (RawState.ofData n base q1).right (h_c :: tail_c) := by
        rw [hst_q1, hst4]; exact hcirc_c
      obtain ⟨q2, t4, hbr_q2, hmod_q2, ⟨r_c, hr_c_eq, hr_c_mem, hst_q2⟩, hcirc_q2⟩ :=
        insertIntoNonEmptyList_exec hb_q1 hbr_q1 (by decide) (by decide) (by decide) (by decide)
          hq1_s6 hq1_s5 hcirc_q1 hw2_not_ht
      rw [hst_q1, hst4] at hr_c_eq hst_q2
      have hb_q2 : q2.Bounded w := t4.bounded hb_q1
      have hq2_s1 : q2.regs s1 = curD := by
        have h42 := t4.regs_eq (insertIntoNonEmptyList_preserves
          (by decide : s1 ≠ s0) (by decide : s1 ≠ s2))
        simp only [h42, q1, Data.set_regs, Function.update_of_ne (by decide : s1 ≠ s6),
          Function.update_of_ne (by decide : s1 ≠ s0), ha4_s1]
      have hq2_s4 : q2.regs s4 = w1.val := by
        have h42 := t4.regs_eq (insertIntoNonEmptyList_preserves
          (by decide : s4 ≠ s0) (by decide : s4 ≠ s2))
        simp only [h42, q1, Data.set_regs, Function.update_of_ne (by decide : s4 ≠ s6),
          Function.update_of_ne (by decide : s4 ≠ s0), ha4_s4]
      let a5 := ((q2.set s1 (curD + 1)).set s0 (base + 5 * n + w1.val)).write
        (base + 5 * n + w1.val) (curD + 1)
      have t5 : ExecWithin w (.op (.exactBin .add s1 s1 oneP)) q2 (q2.set s1 (curD + 1)) 1 := by
        have ho_q2 : q2.regs oneP = 1 := hbr_q2.2.2.2.2.2.2.2.2.2.2.2.2
        simpa only [hq2_s1, ho_q2] using
          execWithin_exactAdd (x := q2) (d := s1) (i := s1) (j := oneP)
            (by rw [hq2_s1, ho_q2]; exact hfit_n1.of_le (by omega))
      have t6 : ExecWithin w (.op (.exactBin .add s0 degBase s4)) (q2.set s1 (curD + 1))
          ((q2.set s1 (curD + 1)).set s0 (base + 5 * n + w1.val)) 1 := by
        have hd_q2 : (q2.set s1 (curD + 1)).regs degBase = base + 5 * n :=
          hbr_q2.2.2.2.2.2.2.2.1
        have hs4_q2 : (q2.set s1 (curD + 1)).regs s4 = w1.val := by
          simp only [Data.set_regs, Function.update_of_ne (by decide : s4 ≠ s1), hq2_s4]
        simpa only [hd_q2, hs4_q2] using
          execWithin_exactAdd (x := q2.set s1 (curD + 1)) (d := s0) (i := degBase) (j := s4)
            (by rw [hd_q2, hs4_q2]; exact hfit_stop.of_le (by simp only [space]; omega))
      have t7 : ExecWithin (B := .exact) w (.op (.store s0 s1))
          ((q2.set s1 (curD + 1)).set s0 (base + 5 * n + w1.val)) a5 1 := by
        have hs1_q2 : ((q2.set s1 (curD + 1)).set s0 (base + 5 * n + w1.val)).regs s1 =
            curD + 1 := by
          simp only [Data.set_regs, Function.update_of_ne (by decide : s1 ≠ s0),
            Function.update_self]
        simpa only [Data.set_regs, Function.update_self, hs1_q2] using
          (ExecWithin.store (B := .exact) (w := w)
            (x := (q2.set s1 (curD + 1)).set s0 (base + 5 * n + w1.val)) (a := s0) (s := s1))
      have he_neg := t1.seq <| t2.seq <| t3.seq <| t4.seq <| t5.seq <| t6.seq t7
      have he5 : ExecWithin w cStep5 a4 a5 18 :=
        (ExecWithin.branch_neg hc5 he_neg).mono (by omega)
      have hbr5 : BaseRegs n base a5 :=
        (((hbr_q2.set_non_base (by decide) _).set_non_base (by decide) _).write_eq _ _)
      have hmod5 : Modifies (Block.mk base (space n)).footprint a4.mem a5.mem := by
        have hm_q1_q2 : Modifies (Block.mk base (space n)).footprint a4.mem q2.mem := hmod_q2
        have hm_q2_a5 : Modifies (Block.mk base (space n)).footprint q2.mem a5.mem :=
          Modifies.write_of_owns ho_dw1 (curD + 1)
        exact modifies_block_trans hm_q1_q2 hm_q2_a5
      have hst5 : RawState.ofData n base a5 =
          { st with
            par := Function.update st.par w2 (w1.val + 1)
            left := Function.update (Function.update st.left w2 h_c.val) r_c w2.val
            right := Function.update (Function.update st.right w2 r_c.val) h_c w2.val
            deg := Function.update st.deg w1 (curD + 1)
            cons := Function.update st.cons curD 0 } := by
        simp only [a5, ofData_write_deg, ofData_set_scratch _ (by decide : 17 ≤ s0.val),
          ofData_set_scratch _ (by decide : 17 ≤ s1.val), hst_q2]
      have hperm_next : (h_c :: w2 :: tail_c).Perm ((T₁.children ++ [T₂]).map FHTree.root) := by
        rw [List.map_append, List.map_singleton]
        exact (List.Perm.swap w2 h_c tail_c).trans
          ((hperm_c.cons w2).trans (List.perm_append_singleton w2 _).symm)
      obtain ⟨c_hc, hc_hc_mem, hc_hc_root⟩ := List.mem_map.mp (hperm_c.subset List.mem_cons_self)
      obtain ⟨c_rc, hc_rc_mem, hc_rc_root⟩ := List.mem_map.mp (hperm_c.subset hr_c_mem)
      have hvalid5 : ValidRoot (RawState.ofData n base a5) none T_next := by
        rw [hst5]
        dsimp only [w1, w2]
        have hcirc5 : IsCircList
            (Function.update (Function.update st.left T₂.root h_c.val) r_c T₂.root.val)
            (Function.update (Function.update st.right T₂.root r_c.val) h_c T₂.root.val)
            (h_c :: w2 :: tail_c) := by
          rw [hst_q2] at hcirc_q2; exact hcirc_q2
        refine hT₁.link hT₂ hnd12 (hd₁.trans hd₂.symm) hprio12
          (fun _ _ => ⟨rfl, rfl, rfl⟩)
          ⟨by dsimp only; rw [hd₁, Function.update_self],
           fun x _ hx => Function.update_of_ne hx _ _⟩
          ⟨by dsimp only; rw [Function.update_of_ne hw1_ne_w2]; exact hT₁.2.1,
           Function.update_self _ _ _,
           fun x _ hx => Function.update_of_ne hx _ _⟩
          ⟨⟨h_c, w2 :: tail_c, hcw1_eq, hcirc5, hperm_next⟩, fun _ _ _ => rfl⟩
          (fun x _ hxw2 hx_not_sib => ?_)
        have hxh : x ≠ h_c := hc_hc_root ▸ hx_not_sib c_hc hc_hc_mem
        have hxr : x ≠ r_c := hc_rc_root ▸ hx_not_sib c_rc hc_rc_mem
        exact ⟨by simp only [Function.update_of_ne hxr, Function.update_of_ne hxw2],
          by simp only [Function.update_of_ne hxh, Function.update_of_ne hxw2]⟩
      refine ⟨a5, he5, he5.bounded hb4, hbr5, hmod5, ?_, ?_, hvalid5, ?_⟩
      · intro r hr
        have ne0 : r ≠ s0 := fun e => by subst e; change 35 < 35 at hr; omega
        have ne1 : r ≠ s1 := fun e => by subst e; change 36 < 35 at hr; omega
        have ne2 : r ≠ s2 := fun e => by subst e; change 37 < 35 at hr; omega
        have ne6 : r ≠ s6 := fun e => by subst e; change 41 < 35 at hr; omega
        have hq2_r := t4.regs_eq (insertIntoNonEmptyList_preserves ne0 ne2)
        simp only [a5, Data.write_regs, Data.set_regs, Function.update_of_ne ne0,
          Function.update_of_ne ne1, hq2_r, q1, Function.update_of_ne ne6, ha4_low r hr]
      · simp only [a5, Data.write_regs, Data.set_regs,
          Function.update_of_ne (by decide : s4 ≠ s0),
          Function.update_of_ne (by decide : s4 ≠ s1), hq2_s4, w1]
      · dsimp only
        rw [hst5]
        refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun u hu => ?_⟩
        have hu1 : u ≠ w1 := fun e => hu (List.mem_append_left _ (e ▸ T₁.root_mem_nodes))
        have hu2 : u ≠ w2 := fun e => hu (List.mem_append_right _ (e ▸ T₂.root_mem_nodes))
        have huh : u ≠ h_c := fun e => hu (List.mem_append_left _
          (T₁.nodes_eq ▸ List.mem_cons_of_mem w1 (mem_forestNodes_iff.mpr
            ⟨c_hc, hc_hc_mem, e.trans hc_hc_root.symm ▸ c_hc.root_mem_nodes⟩)))
        have hur : u ≠ r_c := fun e => hu (List.mem_append_left _
          (T₁.nodes_eq ▸ List.mem_cons_of_mem w1 (mem_forestNodes_iff.mpr
            ⟨c_rc, hc_rc_mem, e.trans hc_rc_root.symm ▸ c_rc.root_mem_nodes⟩)))
        exact ⟨Function.update_of_ne hu2 _ _, rfl,
          by simp only [Function.update_of_ne hur, Function.update_of_ne hu2],
          by simp only [Function.update_of_ne huh, Function.update_of_ne hu2],
          Function.update_of_ne hu1 _ _⟩
  obtain ⟨a5, e5, hb5, hbr5, hmod5, ha5_low, ha5_s4, hvalid5, hst5_props⟩ := hstep5
  dsimp only at hst5_props
  rcases hst5_props with ⟨hk5, hmk5, hin5, hco5, hmin5, hnr5, hnm5, hsz5, hfr5⟩
  -- Step 6 (`a5 → a6`, 3 steps): `curDReg ← curDReg + oneP; s0 ← consBase + curDReg; s3 ← *s0`
  have ha5_curD : a5.regs curDReg = curD := (ha5_low curDReg (by decide)).trans ha_curD
  have ha5_maxD : a5.regs maxDegReg = maxDeg := (ha5_low maxDegReg (by decide)).trans ha_maxD
  let a6 := ((a5.set curDReg (curD + 1)).set s0 (base + 8 * n + (curD + 1))).set s3
    ((RawState.ofData n base a5).cons (curD + 1))
  have e6_1 : ExecWithin w (.op (.exactBin .add curDReg curDReg oneP)) a5
      (a5.set curDReg (curD + 1)) 1 := by
    have ho_5 : a5.regs oneP = 1 := hbr5.2.2.2.2.2.2.2.2.2.2.2.2
    simpa only [ha5_curD, ho_5] using
      execWithin_exactAdd (x := a5) (d := curDReg) (i := curDReg) (j := oneP)
        (by rw [ha5_curD, ho_5]; exact hfit_n1.of_le (by omega))
  have e6_2 : ExecWithin w (.op (.exactBin .add s0 consBase curDReg))
      (a5.set curDReg (curD + 1))
      ((a5.set curDReg (curD + 1)).set s0 (base + 8 * n + (curD + 1))) 1 := by
    have hcb_5 : (a5.set curDReg (curD + 1)).regs consBase = base + 8 * n :=
      hbr5.2.2.2.2.2.2.2.2.2.2.1
    have hcd_5 : (a5.set curDReg (curD + 1)).regs curDReg = curD + 1 := by
      simp only [Data.set_regs, Function.update_self]
    simpa only [hcb_5, hcd_5] using
      execWithin_exactAdd (x := a5.set curDReg (curD + 1))
        (d := s0) (i := consBase) (j := curDReg)
        (by rw [hcb_5, hcd_5]; exact hfit_stop.of_le (by simp only [space]; omega))
  have e6_3 : ExecWithin (B := .exact) w (.op (.load s3 s0))
      ((a5.set curDReg (curD + 1)).set s0 (base + 8 * n + (curD + 1))) a6 1 := by
    have hm_c1 : a5.mem (base + 8 * n + (curD + 1)) =
        (RawState.ofData n base a5).cons (curD + 1) := by
      simp only [RawState.ofData, hd1_le_n, ↓reduceIte]
    simpa only [a6, Data.set_mem, Data.set_regs, Function.update_self, hm_c1] using
      (ExecWithin.load (B := .exact) (w := w)
        (x := (a5.set curDReg (curD + 1)).set s0 (base + 8 * n + (curD + 1)))
        (d := s3) (a := s0))
  have hb6 : a6.Bounded w := e6_3.bounded (e6_2.bounded (e6_1.bounded hb5))
  have hbr6 : BaseRegs n base a6 :=
    ((hbr5.set_non_base (by decide) _).set_non_base (by decide) _).set_non_base (by decide) _
  have hst6 : RawState.ofData n base a6 = RawState.ofData n base a5 := by
    simp only [a6, ofData_set_scratch _ (by decide : 17 ≤ s3.val),
      ofData_set_scratch _ (by decide : 17 ≤ s0.val),
      ofData_set_scratch _ (by decide : 17 ≤ curDReg.val)]
  have he_all : ExecWithin w scatterBody a a6 43 := by
    unfold scatterBody
    exact (e1_1.seq <| e1_2.seq <| e1_3.seq <| e2_1.seq <| e2_2.seq <| e2_3.seq <|
      e2_4.seq <| e2_5.seq <| e3.seq <| e4_1.seq <| e4_2.seq <| e4_3.seq <| e4_4.seq <|
      e4_5.seq <| e5.seq <| e6_1.seq <| e6_2.seq e6_3).mono (by omega)
  have hperm_nodes :
      (T_next.nodes ++ forestNodes slotTrees').Perm (T_cur.nodes ++ forestNodes slotTrees) := by
    rw [hT_next_nodes]
    have hp1 : ((T₁.nodes ++ T₂.nodes) ++ forestNodes slotTrees').Perm
        ((T_cur.nodes ++ T_slot.nodes) ++ forestNodes slotTrees') :=
      hperm12.append_right (forestNodes slotTrees')
    simp only [List.append_assoc] at hp1 ⊢
    exact hp1.trans (hperm_er.append_left T_cur.nodes)
  have hnd_next : (T_next.nodes ++ (forestNodes slotTrees' ++ otherNodes)).Nodup := by
    rw [hT_next_nodes]
    exact ((hperm12.append_right (forestNodes slotTrees' ++ otherNodes)).nodup_iff).mpr hnd_assoc
  have hdisj_ro : ∀ u ∈ forestNodes slotTrees' ++ otherNodes, u ∉ T₁.nodes ++ T₂.nodes :=
    fun u hu hm => (List.nodup_append.mp (hT_next_nodes ▸ hnd_next)).2.2 u hm u hu rfl
  have hs6 : SlotInv n (RawState.ofData n base a6) slotTrees' maxDeg := by
    rw [hst6]
    refine hs.step_collision hidx hslot_deg hd_le_n hno_other hco5 fun R hR => ?_
    obtain ⟨j, hj, _, hR_eq⟩ := List.mem_eraseIdx_iff_getElem.mp hR
    have hR_st : ValidRoot st none R := (hs.2.1 R (hR_eq ▸ List.getElem_mem hj)).1
    refine hR_st.frame_nodes fun u hu => ?_
    have hu_out : u ∉ T₁.nodes ++ T₂.nodes :=
      hdisj_ro u (List.mem_append_left _ (mem_forestNodes_iff.mpr ⟨R, hR, hu⟩))
    have hf := hfr5 u hu_out
    exact ⟨by rw [hin5], by rw [hmk5], hf.2.2.2.2, hf.2.1, by rw [hk5], hf.1, hf.2.2.1, hf.2.2.2.1⟩
  refine ⟨a6, T_next, slotTrees', he_all, hb6, hbr6, modifies_block_trans hmod4 hmod5, ?_, ?_,
    hlen_er, hperm_nodes, hnd_next, hs6, hst6 ▸ hvalid5, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr
    have ne_cd : r ≠ curDReg := fun e => by subst e; change 34 < 33 at hr; omega
    have ne0 : r ≠ s0 := fun e => by subst e; change 35 < 33 at hr; omega
    have ne3 : r ≠ s3 := fun e => by subst e; change 38 < 33 at hr; omega
    simp only [a6, Data.set_regs, Function.update_of_ne ne3, Function.update_of_ne ne0,
      Function.update_of_ne ne_cd, ha5_low r (by omega)]
  · simp only [a6, Data.set_regs, Function.update_of_ne (by decide : maxDegReg ≠ s3),
      Function.update_of_ne (by decide : maxDegReg ≠ s0),
      Function.update_of_ne (by decide : maxDegReg ≠ curDReg), ha5_maxD]
  · dsimp only [T_next]
    cases T₁ with
    | node _ cs =>
      simp only [FHTree.deg_node, FHTree.children_node, List.length_append,
        List.length_singleton] at hd₁ ⊢
      omega
  · simp only [a6, Data.set_regs, Function.update_of_ne (by decide : s4 ≠ s3),
      Function.update_of_ne (by decide : s4 ≠ s0),
      Function.update_of_ne (by decide : s4 ≠ curDReg), ha5_s4, T_next, FHTree.root_node]
  · simp only [a6, Data.set_regs, Function.update_of_ne (by decide : curDReg ≠ s3),
      Function.update_of_ne (by decide : curDReg ≠ s0), Function.update_self]
  · simp only [a6, Data.set_regs, Function.update_self, hst6]
  · dsimp only
    rw [hst6]
    exact ⟨hk5, hmk5, hin5, hmin5, hnr5, hnm5, hsz5,
      fun u hu => hfr5 u (hdisj_ro u (List.mem_append_right _ hu))⟩

/-- Full `while zeroP < s3 do scatterBody` loop by induction on `slotTrees.length`: terminates at an
unoccupied degree slot `curD_f` in `t + 50 * slotTrees_f.length ≤ 2 + 50 * slotTrees.length`
instructions. -/
private theorem scatterLoop_exec {n base w maxDeg : ℕ} {otherNodes : List (Fin n)} {z : Fin n}
    (hz_mem : z ∈ otherNodes) :
    ∀ (k : ℕ) {a : Data rFib} {T_cur : FHTree n} {slotTrees : List (FHTree n)} {curD : ℕ},
      slotTrees.length = k →
      a.Bounded w → BaseRegs n base a →
      (T_cur.nodes ++ (forestNodes slotTrees ++ otherNodes)).Nodup →
      SlotInv n (RawState.ofData n base a) slotTrees maxDeg →
      ValidRoot (RawState.ofData n base a) none T_cur →
      T_cur.deg = curD →
      a.regs s4 = T_cur.root.val →
      a.regs curDReg = curD →
      a.regs maxDegReg = maxDeg →
      a.regs s3 = (RawState.ofData n base a).cons curD →
      ∃ z_lp T_f slotTrees_f curD_f t,
        ExecWithin w (.loop (.lt zeroP s3) scatterBody) a z_lp t ∧
        t + slotCredit * slotTrees_f.length ≤ 2 + slotCredit * slotTrees.length ∧
        ¬(Cond.lt zeroP s3).Holds z_lp ∧
        z_lp.Bounded w ∧ BaseRegs n base z_lp ∧
        Modifies (Block.mk base (space n)).footprint a.mem z_lp.mem ∧
        (∀ r : Fin rFib, r.val < 33 → z_lp.regs r = a.regs r) ∧
        z_lp.regs maxDegReg = maxDeg ∧
        (T_f.nodes ++ forestNodes slotTrees_f).Perm (T_cur.nodes ++ forestNodes slotTrees) ∧
        (T_f.nodes ++ (forestNodes slotTrees_f ++ otherNodes)).Nodup ∧
        SlotInv n (RawState.ofData n base z_lp) slotTrees_f maxDeg ∧
        ValidRoot (RawState.ofData n base z_lp) none T_f ∧
        T_f.deg = curD_f ∧
        z_lp.regs s4 = T_f.root.val ∧
        z_lp.regs curDReg = curD_f ∧
        z_lp.regs s3 = (RawState.ofData n base z_lp).cons curD_f ∧
        (let st := RawState.ofData n base a
         let st' := RawState.ofData n base z_lp
         st'.key = st.key ∧ st'.mark = st.mark ∧ st'.inHeap = st.inHeap ∧
         st'.minRoot = st.minRoot ∧ st'.numRoots = st.numRoots ∧
         st'.numMarked = st.numMarked ∧ st'.sz = st.sz ∧
         ∀ u ∈ otherNodes,
           st'.par u = st.par u ∧ st'.child u = st.child u ∧
           st'.left u = st.left u ∧ st'.right u = st.right u ∧ st'.deg u = st.deg u)
  | 0, a, T_cur, slotTrees, curD, hk, hb, hbr, hnd, hs, hT_cur, hcd, hs4, hcd_r, hmd_r,
      hs3 => by
    by_cases hc : (Cond.lt zeroP s3).Holds a
    · obtain ⟨_, _, slotTrees', _, _, _, _, _, _, hlen_er, _, _, _, _, _, _, _, _, _⟩ :=
        scatterBody_exec hb hbr hz_mem hnd hs hT_cur hcd hs4 hcd_r hmd_r hs3 hc
      omega
    · exact ⟨a, T_cur, slotTrees, curD, 2, ExecWithin.loop_exit hc, by omega, hc, hb, hbr,
        Modifies.refl _ _, fun _ _ => rfl, hmd_r, List.Perm.refl _, hnd, hs, hT_cur, hcd, hs4,
        hcd_r, hs3, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl⟩⟩⟩
  | k + 1, a, T_cur, slotTrees, curD, hk, hb, hbr, hnd, hs, hT_cur, hcd, hs4, hcd_r, hmd_r,
      hs3 => by
    by_cases hc : (Cond.lt zeroP s3).Holds a
    · obtain ⟨a', T_next, slotTrees', he1, hb', hbr', hmod1, hlow1, hmd1, hlen_er, hperm1,
        hnd1, hs1, hT1, hdeg1, hs4_1, hcd1, hs3_1, hfr1⟩ :=
        scatterBody_exec hb hbr hz_mem hnd hs hT_cur hcd hs4 hcd_r hmd_r hs3 hc
      dsimp only at hfr1
      rcases hfr1 with ⟨hk1, hmk1, hin1, hmin1, hnr1, hnm1, hsz1, ho1⟩
      obtain ⟨z_lp, T_f, slotTrees_f, curD_f, t₂, he2, ht2, hnc, hbz, hbrz, hmod2, hlow2, hmd2,
        hperm2, hnd2, hs2, hT2, hdeg2, hs4_2, hcd2, hs3_2, hfr2⟩ :=
        scatterLoop_exec hz_mem k (by omega) hb' hbr' hnd1 hs1 hT1 hdeg1 hs4_1 hcd1 hmd1 hs3_1
      dsimp only at hfr2
      rcases hfr2 with ⟨hk2, hmk2, hin2, hmin2, hnr2, hnm2, hsz2, ho2⟩
      refine ⟨z_lp, T_f, slotTrees_f, curD_f, 43 + t₂ + 2, ExecWithin.loop_iter hc he1 he2,
        by dsimp only [slotCredit] at ht2 ⊢; omega, hnc, hbz, hbrz,
        modifies_block_trans hmod1 hmod2,
        fun r hr => (hlow2 r hr).trans (hlow1 r hr), hmd2, hperm2.trans hperm1, hnd2, hs2, hT2,
        hdeg2, hs4_2, hcd2, hs3_2, ?_⟩
      dsimp only
      refine ⟨hk2.trans hk1, hmk2.trans hmk1, hin2.trans hin1, hmin2.trans hmin1,
        hnr2.trans hnr1, hnm2.trans hnm1, hsz2.trans hsz1, fun u hu => ?_⟩
      have p1 := ho1 u hu
      have p2 := ho2 u hu
      exact ⟨p2.1.trans p1.1, p2.2.1.trans p1.2.1, p2.2.2.1.trans p1.2.2.1,
        p2.2.2.2.1.trans p1.2.2.2.1, p2.2.2.2.2.trans p1.2.2.2.2⟩
    · exact ⟨a, T_cur, slotTrees, curD, 2, ExecWithin.loop_exit hc, by omega, hc, hb, hbr,
        Modifies.refl _ _, fun _ _ => rfl, hmd_r, List.Perm.refl _, hnd, hs, hT_cur, hcd, hs4,
        hcd_r, hs3, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl⟩⟩⟩

/-- `scatterRootCode` inserts root `T₀` (`iterCur = T₀.root.val`) into `cons`, linking equal-degree
roots and updating `maxDegReg` in `t + 50 * slotTrees'.length ≤ 63 + 50 * slotTrees₀.length`
instructions while preserving all registers `< 33` and framing `otherNodes`. -/
theorem scatterRootCode_exec {n base w maxDeg₀ : ℕ} {x : Data rFib}
    {T₀ : FHTree n} {slotTrees₀ : List (FHTree n)} {otherNodes : List (Fin n)} {z : Fin n}
    (hb : x.Bounded w) (hbr : BaseRegs n base x)
    (hz_mem : z ∈ otherNodes)
    (hnd : (T₀.nodes ++ (forestNodes slotTrees₀ ++ otherNodes)).Nodup)
    (hs : SlotInv n (RawState.ofData n base x) slotTrees₀ maxDeg₀)
    (hT₀ : ValidRoot (RawState.ofData n base x) none T₀)
    (hx_ic : x.regs iterCur = T₀.root.val)
    (hx_md : x.regs maxDegReg = maxDeg₀) :
    ∃ y slotTrees' maxDeg' t,
      ExecWithin w scatterRootCode x y t ∧
      t + slotCredit * slotTrees'.length ≤ 63 + slotCredit * slotTrees₀.length ∧
      y.Bounded w ∧ BaseRegs n base y ∧
      Modifies (Block.mk base (space n)).footprint x.mem y.mem ∧
      (∀ r : Fin rFib, r.val < 33 → y.regs r = x.regs r) ∧
      y.regs maxDegReg = maxDeg' ∧
      (forestNodes slotTrees').Perm (T₀.nodes ++ forestNodes slotTrees₀) ∧
      (forestNodes slotTrees' ++ otherNodes).Nodup ∧
      SlotInv n (RawState.ofData n base y) slotTrees' maxDeg' ∧
      (let st := RawState.ofData n base x
       let st' := RawState.ofData n base y
       st'.key = st.key ∧ st'.mark = st.mark ∧ st'.inHeap = st.inHeap ∧
       st'.minRoot = st.minRoot ∧ st'.numRoots = st.numRoots ∧
       st'.numMarked = st.numMarked ∧ st'.sz = st.sz ∧
       ∀ u ∈ otherNodes,
         st'.par u = st.par u ∧ st'.child u = st.child u ∧
         st'.left u = st.left u ∧ st'.right u = st.right u ∧ st'.deg u = st.deg u) := by
  set st := RawState.ofData n base x with hst_def
  have hfit_stop := hbr.fits_stop hb
  have hfit_n1 : Fits w (n + 1) := hfit_stop.of_le (by simp only [space]; omega)
  let u0 := T₀.root
  have hu0_lt := u0.isLt
  let d0 := T₀.deg
  have hnd_0 := List.nodup_append.mp hnd
  have hz_not_0 : z ∉ T₀.nodes := fun hm =>
    hnd_0.2.2 z hm z (List.mem_append_right _ hz_mem) rfl
  have hd0_bds := deg_bounds_of_extra hT₀.1 (List.nodup_cons.mpr ⟨hz_not_0, hnd_0.1⟩)
  have hd0_le_n : d0 ≤ n := by omega
  have hdeg_u0 : st.deg u0 = d0 := by
    cases hT₀.1 with
    | mk _ _ hdeg_eq _ _ _ _ _ => exact hdeg_eq
  -- Preamble (`x → x1`, 5 steps): load `d0 ← deg[iterCur]` and `s3 ← cons[d0]`
  let x1 := ((((x.set s4 u0.val).set s0 (base + 5 * n + u0.val)).set curDReg d0).set s0
    (base + 8 * n + d0)).set s3 (st.cons d0)
  have p1 : ExecWithin (B := .exact) w (.op (.copy s4 iterCur)) x (x.set s4 u0.val) 1 := by
    simpa only [hx_ic] using
      (ExecWithin.copy (B := .exact) (w := w) (x := x) (d := s4) (s := iterCur))
  have p2 : ExecWithin w (.op (.exactBin .add s0 degBase s4)) (x.set s4 u0.val)
      ((x.set s4 u0.val).set s0 (base + 5 * n + u0.val)) 1 := by
    have hdb : (x.set s4 u0.val).regs degBase = base + 5 * n := hbr.2.2.2.2.2.2.2.1
    have hs4 : (x.set s4 u0.val).regs s4 = u0.val := by
      simp only [Data.set_regs, Function.update_self]
    simpa only [hdb, hs4] using
      execWithin_exactAdd (x := x.set s4 u0.val) (d := s0) (i := degBase) (j := s4)
        (by rw [hdb, hs4]; exact hfit_stop.of_le (by simp only [space]; omega))
  have p3 : ExecWithin (B := .exact) w (.op (.load curDReg s0))
      ((x.set s4 u0.val).set s0 (base + 5 * n + u0.val))
      (((x.set s4 u0.val).set s0 (base + 5 * n + u0.val)).set curDReg d0) 1 := by
    have hm_du0 : x.mem (base + 5 * n + u0.val) = d0 := hdeg_u0
    simpa only [Data.set_mem, Data.set_regs, Function.update_self, hm_du0] using
      (ExecWithin.load (B := .exact) (w := w)
        (x := (x.set s4 u0.val).set s0 (base + 5 * n + u0.val)) (d := curDReg) (a := s0))
  have p4 : ExecWithin w (.op (.exactBin .add s0 consBase curDReg))
      (((x.set s4 u0.val).set s0 (base + 5 * n + u0.val)).set curDReg d0)
      ((((x.set s4 u0.val).set s0 (base + 5 * n + u0.val)).set curDReg d0).set s0
        (base + 8 * n + d0)) 1 := by
    have hcb : (((x.set s4 u0.val).set s0 (base + 5 * n + u0.val)).set curDReg d0).regs
        consBase = base + 8 * n := hbr.2.2.2.2.2.2.2.2.2.2.1
    have hcd : (((x.set s4 u0.val).set s0 (base + 5 * n + u0.val)).set curDReg d0).regs
        curDReg = d0 := by simp only [Data.set_regs, Function.update_self]
    simpa only [hcb, hcd] using
      execWithin_exactAdd
        (x := ((x.set s4 u0.val).set s0 (base + 5 * n + u0.val)).set curDReg d0)
        (d := s0) (i := consBase) (j := curDReg)
        (by rw [hcb, hcd]; exact hfit_stop.of_le (by simp only [space]; omega))
  have p5 : ExecWithin (B := .exact) w (.op (.load s3 s0))
      ((((x.set s4 u0.val).set s0 (base + 5 * n + u0.val)).set curDReg d0).set s0
        (base + 8 * n + d0)) x1 1 := by
    have hm_cd0 : x.mem (base + 8 * n + d0) = st.cons d0 := by
      simp only [st, RawState.ofData, hd0_le_n, ↓reduceIte]
    simpa only [x1, Data.set_mem, Data.set_regs, Function.update_self, hm_cd0] using
      (ExecWithin.load (B := .exact) (w := w)
        (x := (((x.set s4 u0.val).set s0 (base + 5 * n + u0.val)).set curDReg d0).set s0
          (base + 8 * n + d0)) (d := s3) (a := s0))
  have hb1 : x1.Bounded w := p5.bounded (p4.bounded (p3.bounded (p2.bounded (p1.bounded hb))))
  have hbr1 : BaseRegs n base x1 :=
    ((((hbr.set_non_base (by decide) _).set_non_base (by decide) _).set_non_base
      (by decide) _).set_non_base (by decide) _).set_non_base (by decide) _
  have hst1 : RawState.ofData n base x1 = st := by
    simp only [x1, ofData_set_scratch _ (by decide : 17 ≤ s3.val),
      ofData_set_scratch _ (by decide : 17 ≤ s0.val),
      ofData_set_scratch _ (by decide : 17 ≤ curDReg.val),
      ofData_set_scratch _ (by decide : 17 ≤ s4.val), ← hst_def]
  have hx1_s4 : x1.regs s4 = u0.val := by
    simp only [x1, Data.set_regs, Function.update_of_ne (by decide : s4 ≠ s3),
      Function.update_of_ne (by decide : s4 ≠ s0),
      Function.update_of_ne (by decide : s4 ≠ curDReg), Function.update_self]
  have hx1_cd : x1.regs curDReg = d0 := by
    simp only [x1, Data.set_regs, Function.update_of_ne (by decide : curDReg ≠ s3),
      Function.update_of_ne (by decide : curDReg ≠ s0), Function.update_self]
  have hx1_md : x1.regs maxDegReg = maxDeg₀ := by
    simp only [x1, Data.set_regs, Function.update_of_ne (by decide : maxDegReg ≠ s3),
      Function.update_of_ne (by decide : maxDegReg ≠ s0),
      Function.update_of_ne (by decide : maxDegReg ≠ curDReg),
      Function.update_of_ne (by decide : maxDegReg ≠ s4), hx_md]
  have hx1_s3 : x1.regs s3 = (RawState.ofData n base x1).cons d0 := by
    simp only [x1, Data.set_regs, Function.update_self, hst1]
  -- Collision loop (`x1 → z_lp`, `t_lp` steps):
  obtain ⟨z_lp, T_f, slotTrees_f, curD_f, t_lp, he_lp, ht_lp, hnc_lp, hbz, hbrz, hmod_lp,
    hlow_lp, hmd_lp, hperm_lp, hnd_lp, hs_lp, hTf, hdeg_f, hs4_lp, hcd_lp, hs3_lp, hfr_lp⟩ :=
    scatterLoop_exec hz_mem slotTrees₀.length rfl hb1 hbr1 hnd (hst1 ▸ hs) (hst1 ▸ hT₀) rfl
      hx1_s4 hx1_cd hx1_md hx1_s3
  dsimp only at hfr_lp
  rw [hst1] at hfr_lp
  rcases hfr_lp with ⟨hk_lp, hmk_lp, hin_lp, hmin_lp, hnr_lp, hnm_lp, hsz_lp, ho_lp⟩
  set st_lp := RawState.ofData n base z_lp with hst_lp_def
  -- Post-loop (`z_lp → y`, 5 steps): store `uf + 1` in `cons[curD_f]` and update `maxDegReg`
  have hnd_f := List.nodup_append.mp hnd_lp
  have hz_not_f : z ∉ T_f.nodes := fun hm =>
    hnd_f.2.2 z hm z (List.mem_append_right _ hz_mem) rfl
  have hdf_bds := deg_bounds_of_extra hTf.1 (List.nodup_cons.mpr ⟨hz_not_f, hnd_f.1⟩)
  rw [hdeg_f] at hdf_bds
  have hdf_le_n : curD_f ≤ n := by omega
  have hcons_f_zero : st_lp.cons curD_f = 0 := by
    have hz0_lp : z_lp.regs zeroP = 0 := hbrz.2.2.2.2.2.2.2.2.2.2.2.1
    rw [Cond.Holds, hz0_lp, hs3_lp] at hnc_lp
    omega
  have hnone_f : ∀ R ∈ slotTrees_f, R.deg ≠ curD_f := by
    rcases hs_lp.lookup hdf_le_n with ⟨_, hnone⟩ | ⟨_, _, _, hce, _, _⟩
    · exact hnone
    · omega
  let uf := T_f.root
  have huf_lt := uf.isLt
  have ho_cons_f := owns_cons_addr (base := base) hdf_le_n
  let z2 := ((z_lp.set s1 (uf.val + 1)).set s0 (base + 8 * n + curD_f)).write
    (base + 8 * n + curD_f) (uf.val + 1)
  have q1 : ExecWithin w (.op (.exactBin .add s1 s4 oneP)) z_lp (z_lp.set s1 (uf.val + 1)) 1 := by
    have ho_z : z_lp.regs oneP = 1 := hbrz.2.2.2.2.2.2.2.2.2.2.2.2
    simpa only [hs4_lp, ho_z] using
      execWithin_exactAdd (x := z_lp) (d := s1) (i := s4) (j := oneP)
        (by rw [hs4_lp, ho_z]; exact hfit_n1.of_le (by omega))
  have q2 : ExecWithin w (.op (.exactBin .add s0 consBase curDReg)) (z_lp.set s1 (uf.val + 1))
      ((z_lp.set s1 (uf.val + 1)).set s0 (base + 8 * n + curD_f)) 1 := by
    have hcb_z : (z_lp.set s1 (uf.val + 1)).regs consBase = base + 8 * n :=
      hbrz.2.2.2.2.2.2.2.2.2.2.1
    have hcd_z : (z_lp.set s1 (uf.val + 1)).regs curDReg = curD_f := hcd_lp
    simpa only [hcb_z, hcd_z] using
      execWithin_exactAdd (x := z_lp.set s1 (uf.val + 1)) (d := s0) (i := consBase) (j := curDReg)
        (by rw [hcb_z, hcd_z]; exact hfit_stop.of_le (by simp only [space]; omega))
  have q3 : ExecWithin (B := .exact) w (.op (.store s0 s1))
      ((z_lp.set s1 (uf.val + 1)).set s0 (base + 8 * n + curD_f)) z2 1 := by
    have hs1_z : ((z_lp.set s1 (uf.val + 1)).set s0 (base + 8 * n + curD_f)).regs s1 =
        uf.val + 1 := by
      simp only [Data.set_regs, Function.update_of_ne (by decide : s1 ≠ s0), Function.update_self]
    simpa only [Data.set_regs, Function.update_self, hs1_z] using
      (ExecWithin.store (B := .exact) (w := w)
        (x := (z_lp.set s1 (uf.val + 1)).set s0 (base + 8 * n + curD_f)) (a := s0) (s := s1))
  have hb_z2 : z2.Bounded w := q3.bounded (q2.bounded (q1.bounded hbz))
  have hbr_z2 : BaseRegs n base z2 :=
    ((hbrz.set_non_base (by decide) _).set_non_base (by decide) _).write_eq _ _
  have hst_z2 : RawState.ofData n base z2 =
      { st_lp with cons := Function.update st_lp.cons curD_f (uf.val + 1) } := by
    simp only [z2, ofData_write_cons hdf_le_n, ofData_set_scratch _ (by decide : 17 ≤ s0.val),
      ofData_set_scratch _ (by decide : 17 ≤ s1.val), ← hst_lp_def]
  have hz2_md : z2.regs maxDegReg = maxDeg₀ := hmd_lp
  have hz2_cd : z2.regs curDReg = curD_f := hcd_lp
  have hz2_z0 : z2.regs zeroP = 0 := hbr_z2.2.2.2.2.2.2.2.2.2.2.2.1
  have hmax_step : ∃ y,
      ExecWithin (B := .exact) w
        (.branch (.lt maxDegReg curDReg) (.op (.copy maxDegReg curDReg)) (.op (.copy s0 zeroP)))
        z2 y 3 ∧
      y.Bounded w ∧ BaseRegs n base y ∧ y.mem = z2.mem ∧
      RawState.ofData n base y = RawState.ofData n base z2 ∧
      y.regs maxDegReg = max maxDeg₀ curD_f ∧
      (∀ r : Fin rFib, r.val < 33 → y.regs r = z2.regs r) := by
    by_cases hlt_md : maxDeg₀ < curD_f
    · have hc_md : (Cond.lt maxDegReg curDReg).Holds z2 := by
        simp only [Cond.Holds, hz2_md, hz2_cd, hlt_md]
      let y := z2.set maxDegReg curD_f
      have ec : ExecWithin (B := .exact) w (.op (.copy maxDegReg curDReg)) z2 y 1 := by
        simpa only [hz2_cd] using
          (ExecWithin.copy (B := .exact) (w := w) (x := z2) (d := maxDegReg) (s := curDReg))
      have heb : ExecWithin (B := .exact) w
          (.branch (.lt maxDegReg curDReg) (.op (.copy maxDegReg curDReg)) (.op (.copy s0 zeroP)))
          z2 y 3 := (ExecWithin.branch_pos hc_md ec).mono (by omega)
      refine ⟨y, heb, heb.bounded hb_z2, hbr_z2.set_non_base (by decide) curD_f, rfl,
        ofData_set_scratch z2 (by decide : 17 ≤ maxDegReg.val) curD_f,
        by simp only [y, Data.set_regs, Function.update_self]; omega, ?_⟩
      intro r hr
      have ne_md : r ≠ maxDegReg := fun e => by subst e; change 33 < 33 at hr; omega
      simp only [y, Data.set_regs, Function.update_of_ne ne_md]
    · have hc_md : ¬(Cond.lt maxDegReg curDReg).Holds z2 := by
        simp only [Cond.Holds, hz2_md, hz2_cd]; omega
      let y := z2.set s0 0
      have ec : ExecWithin (B := .exact) w (.op (.copy s0 zeroP)) z2 y 1 := by
        simpa only [hz2_z0] using
          (ExecWithin.copy (B := .exact) (w := w) (x := z2) (d := s0) (s := zeroP))
      have heb : ExecWithin (B := .exact) w
          (.branch (.lt maxDegReg curDReg) (.op (.copy maxDegReg curDReg)) (.op (.copy s0 zeroP)))
          z2 y 3 := (ExecWithin.branch_neg hc_md ec).mono (by omega)
      refine ⟨y, heb, heb.bounded hb_z2, hbr_z2.set_non_base (by decide) 0, rfl,
        ofData_set_scratch z2 (by decide : 17 ≤ s0.val) 0,
        by simp only [y, Data.set_regs, Function.update_of_ne (by decide : maxDegReg ≠ s0),
          hz2_md]; omega, ?_⟩
      intro r hr
      have ne0 : r ≠ s0 := fun e => by subst e; change 35 < 33 at hr; omega
      simp only [y, Data.set_regs, Function.update_of_ne ne0]
  obtain ⟨y, q4, hby, hbry, hmemy, hsty, hymd, hy_low⟩ := hmax_step
  have he_all : ExecWithin w scatterRootCode x y (t_lp + 11) := by
    unfold scatterRootCode
    exact (p1.seq <| p2.seq <| p3.seq <| p4.seq <| p5.seq <| he_lp.seq <|
      q1.seq <| q2.seq <| q3.seq q4).mono (by omega)
  have hmod_all : Modifies (Block.mk base (space n)).footprint x.mem y.mem := by
    rw [hmemy]
    have hm_lp : Modifies (Block.mk base (space n)).footprint x.mem z_lp.mem := hmod_lp
    have hm_z2 : Modifies (Block.mk base (space n)).footprint z_lp.mem z2.mem :=
      Modifies.write_of_owns ho_cons_f (uf.val + 1)
    exact modifies_block_trans hm_lp hm_z2
  refine ⟨y, T_f :: slotTrees_f, max maxDeg₀ curD_f, t_lp + 11, he_all,
    by simp only [List.length_cons, slotCredit] at ht_lp ⊢; omega,
    hby, hbry, hmod_all, ?_, hymd, hperm_lp, ?_, ?_, ?_⟩
  · intro r hr
    have ne0 : r ≠ s0 := fun e => by subst e; change 35 < 33 at hr; omega
    have ne1 : r ≠ s1 := fun e => by subst e; change 36 < 33 at hr; omega
    have ne3 : r ≠ s3 := fun e => by subst e; change 38 < 33 at hr; omega
    have ne4 : r ≠ s4 := fun e => by subst e; change 39 < 33 at hr; omega
    have ne_cd : r ≠ curDReg := fun e => by subst e; change 34 < 33 at hr; omega
    rw [hy_low r hr]
    simp only [z2, Data.write_regs, Data.set_regs, Function.update_of_ne ne0,
      Function.update_of_ne ne1, hlow_lp r hr, x1, Function.update_of_ne ne3,
      Function.update_of_ne ne_cd, Function.update_of_ne ne4]
  · simpa only [forestNodes, List.append_assoc] using hnd_lp
  · rw [hsty, hst_z2]
    exact hs_lp.insert_empty hdf_bds.2 hdf_bds.1 hdeg_f hnone_f hTf
  · dsimp only
    rw [hsty, hst_z2]
    exact ⟨hk_lp, hmk_lp, hin_lp, hmin_lp, hnr_lp, hnm_lp, hsz_lp, ho_lp⟩

/-! ## Consolidation scatter loops (`childScatterLoop` and `rootScatterLoop`) -/

private theorem extract_tree_by_root {n : ℕ} {cs : List (FHTree n)} {u : Fin n} {tl : List (Fin n)}
    (hnd : (forestNodes cs).Nodup) (hperm : (u :: tl).Perm (cs.map FHTree.root)) :
    ∃ (i : ℕ) (hi : i < cs.length),
      (cs[i]).root = u ∧
      tl.Perm ((cs.eraseIdx i).map FHTree.root) ∧
      ((cs[i]).nodes ++ forestNodes (cs.eraseIdx i)).Perm (forestNodes cs) := by
  have hu_mem : u ∈ cs.map FHTree.root := hperm.subset List.mem_cons_self
  obtain ⟨T, hT_mem, hT_root⟩ := List.mem_map.mp hu_mem
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hT_mem
  refine ⟨i, hi, hT_root, ?_, forestNodes_eraseIdx_perm cs i hi⟩
  have hnd_map : (cs.map FHTree.root).Nodup := map_root_nodup hnd
  have hi_map : i < (cs.map FHTree.root).length := by simp only [List.length_map]; exact hi
  rw [map_eraseIdx_eq, ← hnd_map.erase_getElem i hi_map, List.getElem_map, hT_root]
  simpa only [List.erase_cons_head] using hperm.erase u

private theorem perm_reassoc_mid {α : Type*} (A B C D : List α) :
    (A ++ (C ++ (B ++ D))).Perm ((A ++ B) ++ (C ++ D)) := by
  have h1 : A ++ (C ++ (B ++ D)) = A ++ ((C ++ B) ++ D) := by simp only [List.append_assoc]
  have h2 : A ++ ((B ++ C) ++ D) = (A ++ B) ++ (C ++ D) := by simp only [List.append_assoc]
  rw [h1, ← h2]
  exact (List.perm_append_comm.append_right D).append_left A

private theorem perm_swap_front {α : Type*} (X Y Z : List α) :
    (X ++ (Y ++ Z)).Perm (Y ++ (X ++ Z)) := by
  rw [← List.append_assoc, ← List.append_assoc]
  exact List.perm_append_comm.append_right Z

private abbrev childScatterBody : Code .exact rFib :=
  ram_exact[
    s0 ← rightBase + iterCur;
    iterNxt ← *s0;
    s0 ← parBase + iterCur;
    *s0 ← zeroP;
    s0 ← markBase + iterCur;
    s1 ← *s0;
    if zeroP < s1 then [
      *s0 ← zeroP;
      numMarkedReg ← numMarkedReg - oneP
    ] else [
      s0 ← zeroP
    ];
    ⟪scatterRootCode⟫;
    iterCur ← iterNxt;
    remReg ← remReg - oneP
  ]

private abbrev childScatterLoop : Code .exact rFib :=
  .loop (.lt zeroP remReg) childScatterBody

/-- Phase A1 loop: detaches each child in `c_trees` along `c_order`, clears its `par` and `mark`
(decrementing `numMarkedReg` when marked), and scatters it into `cons`. -/
private theorem scatterChildrenLoop_exec {n base w : ℕ}
    (c_order : List (Fin n)) :
    ∀ (a : Data rFib) (c_trees slotTrees : List (FHTree n)) (fixedNodes : List (Fin n))
      (z : Fin n) (maxDeg : ℕ),
      a.Bounded w → BaseRegs n base a →
      z ∈ fixedNodes →
      (forestNodes c_trees ++ (forestNodes slotTrees ++ fixedNodes)).Nodup →
      SlotInv n (RawState.ofData n base a) slotTrees maxDeg →
      (∀ c ∈ c_trees, ValidSubtree (RawState.ofData n base a) none c) →
      c_order.Perm (c_trees.map FHTree.root) →
      RightChain (RawState.ofData n base a).right c_order →
      a.regs remReg = c_order.length →
      a.regs maxDegReg = maxDeg →
      (RawState.ofData n base a).numMarked = markedCount (RawState.ofData n base a) →
      (∀ u tl, c_order = u :: tl → a.regs iterCur = u.val) →
      ∃ b slotTrees' maxDeg' t,
        ExecWithin w childScatterLoop a b t ∧
        t + slotCredit * slotTrees'.length ≤
          2 + 76 * c_order.length + slotCredit * slotTrees.length ∧
        b.Bounded w ∧ BaseRegs n base b ∧
        Modifies (Block.mk base (space n)).footprint a.mem b.mem ∧
        (∀ r : Fin rFib, r.val < 30 → r ≠ numMarkedReg → b.regs r = a.regs r) ∧
        b.regs maxDegReg = maxDeg' ∧
        (forestNodes slotTrees').Perm (forestNodes c_trees ++ forestNodes slotTrees) ∧
        (forestNodes slotTrees' ++ fixedNodes).Nodup ∧
        SlotInv n (RawState.ofData n base b) slotTrees' maxDeg' ∧
        (let st := RawState.ofData n base a
         let st' := RawState.ofData n base b
         st'.key = st.key ∧ st'.inHeap = st.inHeap ∧
         st'.minRoot = st.minRoot ∧ st'.numRoots = st.numRoots ∧ st'.sz = st.sz ∧
         st'.numMarked = markedCount st' ∧ st'.numMarked ≤ st.numMarked ∧
         ∀ v ∈ fixedNodes,
           st'.par v = st.par v ∧ st'.child v = st.child v ∧
           st'.left v = st.left v ∧ st'.right v = st.right v ∧
           st'.deg v = st.deg v ∧ st'.mark v = st.mark v) := by
  induction c_order with
  | nil =>
    intro a c_trees slotTrees fixedNodes z maxDeg hb hbr _ hnd hs _ hperm _ hrem hmd hnm _
    have hz0 : a.regs zeroP = 0 := hbr.2.2.2.2.2.2.2.2.2.2.2.1
    have hc : ¬(Cond.lt zeroP remReg).Holds a := by
      simp only [Cond.Holds, hz0, hrem, List.length_nil, Nat.lt_irrefl, not_false_eq_true]
    have hct_nil : c_trees = [] := by
      apply List.eq_nil_of_length_eq_zero
      have hlen := hperm.length_eq
      simp only [List.length_nil, List.length_map] at hlen
      omega
    subst hct_nil
    exact ⟨a, slotTrees, maxDeg, 2, ExecWithin.loop_exit hc, by omega, hb, hbr,
      Modifies.refl _ _, fun _ _ _ => rfl, hmd,
      by simp only [forestNodes, List.nil_append, List.Perm.refl],
      by simpa only [forestNodes, List.nil_append] using hnd,
      hs, ⟨rfl, rfl, rfl, rfl, rfl, hnm, le_rfl, fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩⟩
  | cons u c_tl ih =>
    intro a c_trees slotTrees fixedNodes z maxDeg hb hbr hz_mem hnd hs hsub hperm hchain hrem hmd
      hnm hic
    set st := RawState.ofData n base a with hst_def
    have hfit_stop := hbr.fits_stop hb
    have hz0 : a.regs zeroP = 0 := hbr.2.2.2.2.2.2.2.2.2.2.2.1
    have ho1 : a.regs oneP = 1 := hbr.2.2.2.2.2.2.2.2.2.2.2.2
    have hpb : a.regs parBase = base + n := hbr.2.2.2.1
    have hrb : a.regs rightBase = base + 4 * n := hbr.2.2.2.2.2.2.1
    have hmkb : a.regs markBase = base + 6 * n := hbr.2.2.2.2.2.2.2.2.1
    have hc : (Cond.lt zeroP remReg).Holds a := by
      simp only [Cond.Holds, hz0, hrem, List.length_cons]; omega
    have hu_ic : a.regs iterCur = u.val := hic u c_tl rfl
    have hu_lt := u.isLt
    have hnd_c : (forestNodes c_trees).Nodup := (List.nodup_append.mp hnd).1
    obtain ⟨idx, hidx, hTu_root, hperm_tl, hperm_fn⟩ := extract_tree_by_root hnd_c hperm
    let T_u := c_trees[idx]
    let c_rest := c_trees.eraseIdx idx
    have hTu_sub : ValidSubtree st none T_u := hsub T_u (List.getElem_mem hidx)
    have hTu_r : T_u.root = u := hTu_root
    have hu_bds : st.inHeap u ≠ 0 ∧ st.mark u ≤ 1 := by
      rcases hTu_eq : T_u with ⟨u', cs_u⟩
      have hsub_eq := hTu_sub
      rw [hTu_eq] at hsub_eq
      have hr_eq : u' = u := by simpa only [hTu_eq, FHTree.root_node] using hTu_r
      subst hr_eq
      cases hsub_eq with
      | mk hin hm _ _ _ _ _ _ => exact ⟨hin, hm⟩
    have hnd_split :
        ((T_u.nodes ++ forestNodes c_rest) ++ (forestNodes slotTrees ++ fixedNodes)).Nodup :=
      (hperm_fn.append_right _).nodup_iff.mpr hnd
    have hnd_Tu : T_u.nodes.Nodup := (List.nodup_append.mp (List.nodup_append.mp hnd_split).1).1
    have hu_not_desc : u ∉ forestNodes T_u.children := by
      have hnd_eq := hnd_Tu
      rw [T_u.nodes_eq, hTu_root] at hnd_eq
      exact (List.nodup_cons.mp hnd_eq).1
    have hu_in_Tu : u ∈ T_u.nodes := hTu_root ▸ T_u.root_mem_nodes
    have hu_not_other : u ∉ forestNodes c_rest ++ (forestNodes slotTrees ++ fixedNodes) := by
      have hnd_assoc :
          (T_u.nodes ++ (forestNodes c_rest ++ (forestNodes slotTrees ++ fixedNodes))).Nodup := by
        simpa only [List.append_assoc] using hnd_split
      exact fun hm => (List.nodup_append.mp hnd_assoc).2.2 u hu_in_Tu u hm rfl
    -- Step 1 (`a → a1`, 6 steps): load `iterNxt ← right[u]`, clear `par[u]`, load `s1 ← mark[u]`
    have ho_par_u := owns_arr_addr (base := base) (k := 1) (by decide) hu_lt
    have ho_mk_u := owns_arr_addr (base := base) (k := 6) (by decide) hu_lt
    let nxtVal := st.right u
    let a1 := (((((a.set s0 (base + 4 * n + u.val)).set iterNxt nxtVal).set s0
      (base + n + u.val)).write (base + n + u.val) 0).set s0 (base + 6 * n + u.val)).set s1
      (st.mark u)
    have s1_1 : ExecWithin w (.op (.exactBin .add s0 rightBase iterCur)) a
        (a.set s0 (base + 4 * n + u.val)) 1 := by
      simpa only [hrb, hu_ic] using
        execWithin_exactAdd (x := a) (d := s0) (i := rightBase) (j := iterCur)
          (by rw [hrb, hu_ic]; exact hfit_stop.of_le (by simp only [space]; omega))
    have s1_2 : ExecWithin (B := .exact) w (.op (.load iterNxt s0))
        (a.set s0 (base + 4 * n + u.val))
        ((a.set s0 (base + 4 * n + u.val)).set iterNxt nxtVal) 1 := by
      have hm_r : a.mem (base + 4 * n + u.val) = nxtVal := rfl
      simpa only [Data.set_mem, Data.set_regs, Function.update_self, hm_r] using
        (ExecWithin.load (B := .exact) (w := w) (x := a.set s0 (base + 4 * n + u.val))
          (d := iterNxt) (a := s0))
    have s1_3 : ExecWithin w (.op (.exactBin .add s0 parBase iterCur))
        ((a.set s0 (base + 4 * n + u.val)).set iterNxt nxtVal)
        (((a.set s0 (base + 4 * n + u.val)).set iterNxt nxtVal).set s0 (base + n + u.val)) 1 := by
      have hp_1 : ((a.set s0 (base + 4 * n + u.val)).set iterNxt nxtVal).regs parBase =
          base + n := hpb
      have hic_1 : ((a.set s0 (base + 4 * n + u.val)).set iterNxt nxtVal).regs iterCur =
          u.val := hu_ic
      simpa only [hp_1, hic_1] using
        execWithin_exactAdd (x := (a.set s0 (base + 4 * n + u.val)).set iterNxt nxtVal)
          (d := s0) (i := parBase) (j := iterCur)
          (by rw [hp_1, hic_1]; exact hfit_stop.of_le (by simp only [space]; omega))
    have s1_4 : ExecWithin (B := .exact) w (.op (.store s0 zeroP))
        (((a.set s0 (base + 4 * n + u.val)).set iterNxt nxtVal).set s0 (base + n + u.val))
        ((((a.set s0 (base + 4 * n + u.val)).set iterNxt nxtVal).set s0 (base + n + u.val)).write
          (base + n + u.val) 0) 1 := by
      have hz_1 : (((a.set s0 (base + 4 * n + u.val)).set iterNxt nxtVal).set s0
          (base + n + u.val)).regs zeroP = 0 := hz0
      simpa only [Data.set_regs, Function.update_self, hz_1] using
        (ExecWithin.store (B := .exact) (w := w)
          (x := ((a.set s0 (base + 4 * n + u.val)).set iterNxt nxtVal).set s0 (base + n + u.val))
          (a := s0) (s := zeroP))
    have s1_5 : ExecWithin w (.op (.exactBin .add s0 markBase iterCur))
        ((((a.set s0 (base + 4 * n + u.val)).set iterNxt nxtVal).set s0 (base + n + u.val)).write
          (base + n + u.val) 0)
        (((((a.set s0 (base + 4 * n + u.val)).set iterNxt nxtVal).set s0 (base + n + u.val)).write
          (base + n + u.val) 0).set s0 (base + 6 * n + u.val)) 1 := by
      have hm_1 : ((((a.set s0 (base + 4 * n + u.val)).set iterNxt nxtVal).set s0
          (base + n + u.val)).write (base + n + u.val) 0).regs markBase = base + 6 * n := hmkb
      have hic_1 : ((((a.set s0 (base + 4 * n + u.val)).set iterNxt nxtVal).set s0
          (base + n + u.val)).write (base + n + u.val) 0).regs iterCur = u.val := hu_ic
      simpa only [hm_1, hic_1] using
        execWithin_exactAdd
          (x := (((a.set s0 (base + 4 * n + u.val)).set iterNxt nxtVal).set s0
            (base + n + u.val)).write (base + n + u.val) 0)
          (d := s0) (i := markBase) (j := iterCur)
          (by rw [hm_1, hic_1]; exact hfit_stop.of_le (by simp only [space]; omega))
    have s1_6 : ExecWithin (B := .exact) w (.op (.load s1 s0))
        (((((a.set s0 (base + 4 * n + u.val)).set iterNxt nxtVal).set s0 (base + n + u.val)).write
          (base + n + u.val) 0).set s0 (base + 6 * n + u.val)) a1 1 := by
      have hm_mk : a.mem (base + 6 * n + u.val) = st.mark u := rfl
      simpa only [a1, Data.set_mem, Data.write_mem, Data.set_regs, Function.update_self,
        Function.update_of_ne (by omega : base + 6 * n + u.val ≠ base + n + u.val), hm_mk] using
        (ExecWithin.load (B := .exact) (w := w)
          (x := ((((a.set s0 (base + 4 * n + u.val)).set iterNxt nxtVal).set s0
            (base + n + u.val)).write (base + n + u.val) 0).set s0 (base + 6 * n + u.val))
          (d := s1) (a := s0))
    have he1 : ExecWithin w
        (.seq (.op (.exactBin .add s0 rightBase iterCur)) <|
         .seq (.op (.load iterNxt s0)) <|
         .seq (.op (.exactBin .add s0 parBase iterCur)) <|
         .seq (.op (.store s0 zeroP)) <|
         .seq (.op (.exactBin .add s0 markBase iterCur))
              (.op (.load s1 s0))) a a1 6 :=
      (s1_1.seq <| s1_2.seq <| s1_3.seq <| s1_4.seq <| s1_5.seq s1_6).mono (by omega)
    have hb1 : a1.Bounded w := he1.bounded hb
    have hbr1 : BaseRegs n base a1 :=
      (((((hbr.set_non_base (by decide) _).set_non_base (by decide) _).set_non_base
        (by decide) _).write_eq _ _).set_non_base (by decide) _).set_non_base (by decide) _
    have hmod1 : Modifies (Block.mk base (space n)).footprint a.mem a1.mem := by
      dsimp only [a1]
      simp only [Data.set_mem, Data.write_mem]
      simpa only [Nat.one_mul] using Modifies.write_of_owns ho_par_u 0
    have hst1 : RawState.ofData n base a1 = { st with par := Function.update st.par u 0 } := by
      have hp_wr : RawState.ofData n base (a.write (base + n + u.val) 0) =
          { st with par := Function.update st.par u 0 } := by
        simpa only [Nat.one_mul, ← hst_def] using ofData_write_par a u 0
      simp only [a1, ofData_set_scratch _ (by decide : 17 ≤ s1.val),
        ofData_set_scratch _ (by decide : 17 ≤ s0.val)]
      exact hp_wr
    have ha1_s0 : a1.regs s0 = base + 6 * n + u.val := by
      simp only [a1, Data.set_regs, Function.update_of_ne (by decide : s0 ≠ s1),
        Function.update_self]
    have ha1_s1 : a1.regs s1 = st.mark u := by
      simp only [a1, Data.set_regs, Function.update_self]
    have ha1_z0 : a1.regs zeroP = 0 := hbr1.2.2.2.2.2.2.2.2.2.2.2.1
    have ha1_o1 : a1.regs oneP = 1 := hbr1.2.2.2.2.2.2.2.2.2.2.2.2
    have ha1_nm : a1.regs numMarkedReg = st.numMarked := rfl
    -- Step 2 (`a1 → a_mid`, 3 steps): clear `mark[u]` and decrement `numMarkedReg` if `0 < mark[u]`
    have hmark_step : ∃ a_mid,
        ExecWithin (B := .exact) w
          (.branch (.lt zeroP s1)
            (.seq (.op (.store s0 zeroP)) (.op (.exactBin .sub numMarkedReg numMarkedReg oneP)))
            (.op (.copy s0 zeroP))) a1 a_mid 3 ∧
        a_mid.Bounded w ∧ BaseRegs n base a_mid ∧
        Modifies (Block.mk base (space n)).footprint a1.mem a_mid.mem ∧
        (∀ r : Fin rFib, r ≠ s0 → r ≠ numMarkedReg → a_mid.regs r = a1.regs r) ∧
        (let st_mid := RawState.ofData n base a_mid
         st_mid.key = st.key ∧ st_mid.par = Function.update st.par u 0 ∧
         st_mid.child = st.child ∧ st_mid.left = st.left ∧ st_mid.right = st.right ∧
         st_mid.deg = st.deg ∧ st_mid.inHeap = st.inHeap ∧ st_mid.cons = st.cons ∧
         st_mid.minRoot = st.minRoot ∧ st_mid.numRoots = st.numRoots ∧ st_mid.sz = st.sz ∧
         st_mid.mark u = 0 ∧ (∀ x : Fin n, x ≠ u → st_mid.mark x = st.mark x) ∧
         st_mid.numMarked = markedCount st_mid ∧ st_mid.numMarked ≤ st.numMarked) := by
      by_cases hmk_pos : 0 < st.mark u
      · have hc_mk : (Cond.lt zeroP s1).Holds a1 := by
          simp only [Cond.Holds, ha1_z0, ha1_s1, hmk_pos]
        have hu_in_mk : u ∈ markedSet st := by
          simp only [markedSet, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hu_bds.1, by omega⟩
        have hnm_pos : 1 ≤ st.numMarked := by
          rw [hnm]
          exact Finset.card_pos.mpr ⟨u, hu_in_mk⟩
        let a_mid := (a1.write (base + 6 * n + u.val) 0).set numMarkedReg (st.numMarked - 1)
        have m1 : ExecWithin (B := .exact) w (.op (.store s0 zeroP)) a1
            (a1.write (base + 6 * n + u.val) 0) 1 := by
          simpa only [ha1_s0, ha1_z0] using
            (ExecWithin.store (B := .exact) (w := w) (x := a1) (a := s0) (s := zeroP))
        have m2 : ExecWithin w (.op (.exactBin .sub numMarkedReg numMarkedReg oneP))
            (a1.write (base + 6 * n + u.val) 0) a_mid 1 := by
          have hnm_w : (a1.write (base + 6 * n + u.val) 0).regs numMarkedReg = st.numMarked :=
            ha1_nm
          have ho1_w : (a1.write (base + 6 * n + u.val) 0).regs oneP = 1 := ha1_o1
          simpa only [hnm_w, ho1_w] using
            execWithin_exactSub (x := a1.write (base + 6 * n + u.val) 0)
              (d := numMarkedReg) (i := numMarkedReg) (j := oneP)
              (by rw [hnm_w, ho1_w]; exact hnm_pos)
              (by rw [hnm_w, ho1_w]; exact (hb1.1 numMarkedReg).of_le (by omega))
        have heb : ExecWithin (B := .exact) w
            (.branch (.lt zeroP s1)
              (.seq (.op (.store s0 zeroP)) (.op (.exactBin .sub numMarkedReg numMarkedReg oneP)))
              (.op (.copy s0 zeroP))) a1 a_mid 3 :=
          (ExecWithin.branch_pos hc_mk (m1.seq m2)).mono (by omega)
        have hst_mid : RawState.ofData n base a_mid =
            { st with
              par := Function.update st.par u 0
              mark := Function.update st.mark u 0
              numMarked := st.numMarked - 1 } := by
          simp only [a_mid, ofData_set_numMarked, ofData_write_mark, hst1]
        have hmc_mid : markedCount (RawState.ofData n base a_mid) + 1 = markedCount st := by
          refine markedCount_clear_one hu_bds.1 (by omega)
            (by rw [hst_mid]; dsimp only; rw [Function.update_self]) (fun x hx => ?_)
          rw [hst_mid]
          dsimp only
          rw [Function.update_of_ne hx]
        refine ⟨a_mid, heb, heb.bounded hb1,
          (hbr1.write_eq _ _).set_non_base (by decide) _,
          Modifies.write_of_owns ho_mk_u 0, ?_, ?_⟩
        · intro r _ hne_nm
          simp only [a_mid, Data.set_regs, Data.write_regs, Function.update_of_ne hne_nm]
        · dsimp only
          rw [hst_mid] at hmc_mid ⊢
          dsimp only
          exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
            Function.update_self _ _ _, fun x hx => Function.update_of_ne hx _ _,
            by omega, by omega⟩
      · have hc_mk : ¬(Cond.lt zeroP s1).Holds a1 := by
          simp only [Cond.Holds, ha1_z0, ha1_s1]; omega
        let a_mid := a1.set s0 0
        have m1 : ExecWithin (B := .exact) w (.op (.copy s0 zeroP)) a1 a_mid 1 := by
          simpa only [ha1_z0] using
            (ExecWithin.copy (B := .exact) (w := w) (x := a1) (d := s0) (s := zeroP))
        have heb : ExecWithin (B := .exact) w
            (.branch (.lt zeroP s1)
              (.seq (.op (.store s0 zeroP)) (.op (.exactBin .sub numMarkedReg numMarkedReg oneP)))
              (.op (.copy s0 zeroP))) a1 a_mid 3 :=
          (ExecWithin.branch_neg hc_mk m1).mono (by omega)
        have hst_mid : RawState.ofData n base a_mid =
            { st with par := Function.update st.par u 0 } := by
          rw [ofData_set_scratch a1 (by decide : 17 ≤ s0.val) 0, hst1]
        have hmc_mid : markedCount (RawState.ofData n base a_mid) = markedCount st := by
          apply markedCount_congr
          intro x
          rw [hst_mid]
        refine ⟨a_mid, heb, heb.bounded hb1, hbr1.set_non_base (by decide) 0,
          Modifies.refl _ _, ?_, ?_⟩
        · intro r hne0 _
          simp only [a_mid, Data.set_regs, Function.update_of_ne hne0]
        · dsimp only
          rw [hst_mid] at hmc_mid ⊢
          dsimp only
          exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
            by omega, fun _ _ => rfl, by rw [hmc_mid]; exact hnm, le_rfl⟩
    obtain ⟨a_mid, he2, hb_mid, hbr_mid, hmod2, hregs_mid,
      hk_m, hpar_m, hch_m, hl_m, hr_m, hd_m, hin_m, hcons_m,
      hmin_m, hnr_m, hsz_m, hmu0, hm_other, hnm_m, hnm_le_m⟩ := hmark_step
    -- `T_u` is now a `ValidRoot`, and `slotTrees` / `c_rest` remain valid in `a_mid`
    have hTu_mid : ValidRoot (RawState.ofData n base a_mid) none T_u := by
      refine ⟨hTu_sub.frame_root_mark hnd_Tu (by rw [hTu_r, hmu0]; omega)
        ⟨by rw [hin_m], by rw [hd_m], by rw [hch_m], by rw [hk_m]⟩
        (fun x hx => ?_) (fun x hx => ?_),
        by rw [hpar_m, hTu_r, Function.update_self],
        by rw [hTu_r, hmu0]⟩
      · have hxu : x ≠ u := fun e => hu_not_desc (e ▸ hx)
        exact ⟨by rw [hin_m], hm_other x hxu, by rw [hd_m], by rw [hch_m], by rw [hk_m]⟩
      · have hxu : x ≠ u := fun e => hu_not_desc (e ▸ hx)
        exact ⟨by rw [hpar_m, Function.update_of_ne hxu], by rw [hl_m], by rw [hr_m], Iff.rfl⟩
    have hs_mid : SlotInv n (RawState.ofData n base a_mid) slotTrees maxDeg := by
      refine hs.frame hcons_m fun R hR => (hs.2.1 R hR).1.frame_nodes fun x hx => ?_
      have hxu : x ≠ u := fun e => hu_not_other
        (List.mem_append_right _ (List.mem_append_left _
          (mem_forestNodes_iff.mpr ⟨R, hR, e ▸ hx⟩)))
      exact ⟨by rw [hin_m], hm_other x hxu, by rw [hd_m], by rw [hch_m], by rw [hk_m],
        by rw [hpar_m, Function.update_of_ne hxu], by rw [hl_m], by rw [hr_m]⟩
    -- Step 3 (`a_mid → a_sc`, `t_sc` steps): `scatterRootCode` on `T_u`
    have hnd_for_sc :
        (T_u.nodes ++ (forestNodes slotTrees ++ (forestNodes c_rest ++ fixedNodes))).Nodup :=
      (perm_reassoc_mid T_u.nodes (forestNodes c_rest) (forestNodes slotTrees)
        fixedNodes).nodup_iff.mpr hnd_split
    have hmid_ic : a_mid.regs iterCur = T_u.root.val := by
      rw [hregs_mid iterCur (by decide) (by decide)]
      simp only [a1, Data.set_regs, Data.write_regs,
        Function.update_of_ne (by decide : iterCur ≠ s1),
        Function.update_of_ne (by decide : iterCur ≠ s0),
        Function.update_of_ne (by decide : iterCur ≠ iterNxt), hu_ic, hTu_r]
    have hmid_md : a_mid.regs maxDegReg = maxDeg := by
      rw [hregs_mid maxDegReg (by decide) (by decide)]
      simp only [a1, Data.set_regs, Data.write_regs,
        Function.update_of_ne (by decide : maxDegReg ≠ s1),
        Function.update_of_ne (by decide : maxDegReg ≠ s0),
        Function.update_of_ne (by decide : maxDegReg ≠ iterNxt), hmd]
    obtain ⟨a_sc, slotTrees_1, maxDeg_1, t_sc, he3, ht_sc, hb_sc, hbr_sc, hmod3, hlow_sc,
      hmd_sc, hperm_sc, hnd_sc, hs_sc,
      hk_sc, hmk_sc, hin_sc, hmin_sc, hnr_sc, hnm_sc, hsz_sc, ho_sc⟩ :=
      scatterRootCode_exec hb_mid hbr_mid (List.mem_append_right _ hz_mem)
        hnd_for_sc hs_mid hTu_mid hmid_ic hmid_md
    -- Step 4 (`a_sc → a_next`, 2 steps): `iterCur ← iterNxt; remReg ← remReg - oneP`
    have hsc_nxt : a_sc.regs iterNxt = nxtVal := by
      rw [hlow_sc iterNxt (by decide), hregs_mid iterNxt (by decide) (by decide)]
      simp only [a1, Data.set_regs, Data.write_regs,
        Function.update_of_ne (by decide : iterNxt ≠ s1),
        Function.update_of_ne (by decide : iterNxt ≠ s0), Function.update_self]
    have hsc_rem : a_sc.regs remReg = c_tl.length + 1 := by
      rw [hlow_sc remReg (by decide), hregs_mid remReg (by decide) (by decide)]
      simp only [a1, Data.set_regs, Data.write_regs,
        Function.update_of_ne (by decide : remReg ≠ s1),
        Function.update_of_ne (by decide : remReg ≠ s0),
        Function.update_of_ne (by decide : remReg ≠ iterNxt), hrem, List.length_cons]
    let a_next := (a_sc.set iterCur nxtVal).set remReg c_tl.length
    have s4_1 : ExecWithin (B := .exact) w (.op (.copy iterCur iterNxt)) a_sc
        (a_sc.set iterCur nxtVal) 1 := by
      simpa only [hsc_nxt] using
        (ExecWithin.copy (B := .exact) (w := w) (x := a_sc) (d := iterCur) (s := iterNxt))
    have s4_2 : ExecWithin w (.op (.exactBin .sub remReg remReg oneP))
        (a_sc.set iterCur nxtVal) a_next 1 := by
      have hrem_w : (a_sc.set iterCur nxtVal).regs remReg = c_tl.length + 1 := hsc_rem
      have ho1_w : (a_sc.set iterCur nxtVal).regs oneP = 1 := hbr_sc.2.2.2.2.2.2.2.2.2.2.2.2
      simpa only [hrem_w, ho1_w, Nat.add_sub_cancel] using
        execWithin_exactSub (x := a_sc.set iterCur nxtVal) (d := remReg) (i := remReg) (j := oneP)
          (by rw [hrem_w, ho1_w]; omega)
          (by rw [hrem_w, ho1_w]; exact (hb_sc.1 remReg).of_le (by omega))
    have he_body : ExecWithin w childScatterBody a a_next (t_sc + 11) := by
      unfold childScatterBody
      exact (s1_1.seq <| s1_2.seq <| s1_3.seq <| s1_4.seq <| s1_5.seq <| s1_6.seq <|
        he2.seq <| he3.seq <| s4_1.seq s4_2).mono (by omega)
    have hb_next : a_next.Bounded w := s4_2.bounded (s4_1.bounded hb_sc)
    have hbr_next : BaseRegs n base a_next :=
      (hbr_sc.set_non_base (by decide) _).set_non_base (by decide) _
    have hst_next : RawState.ofData n base a_next = RawState.ofData n base a_sc := by
      simp only [a_next, ofData_set_scratch _ (by decide : 17 ≤ remReg.val),
        ofData_set_scratch _ (by decide : 17 ≤ iterCur.val)]
    -- Prepare induction hypotheses on `a_next`
    have hnd_next : (forestNodes c_rest ++ (forestNodes slotTrees_1 ++ fixedNodes)).Nodup :=
      (perm_swap_front (forestNodes slotTrees_1) (forestNodes c_rest) fixedNodes).nodup_iff.mp
        hnd_sc
    have hs_next : SlotInv n (RawState.ofData n base a_next) slotTrees_1 maxDeg_1 := by
      rw [hst_next]; exact hs_sc
    have hsub_next : ∀ c ∈ c_rest, ValidSubtree (RawState.ofData n base a_next) none c := by
      intro c hc_mem
      obtain ⟨j, hj, _, hc_eq⟩ := List.mem_eraseIdx_iff_getElem.mp hc_mem
      have hc_sub : ValidSubtree st none c := hc_eq ▸ hsub _ (List.getElem_mem hj)
      rw [hst_next]
      refine hc_sub.frame (fun x hx => ?_) (fun x hx => ?_)
      · have hx_rest : x ∈ forestNodes c_rest := mem_forestNodes_iff.mpr ⟨c, hc_mem, hx⟩
        have hxu : x ≠ u := fun e => hu_not_other (List.mem_append_left _ (e ▸ hx_rest))
        have ho_x := ho_sc x (List.mem_append_left _ hx_rest)
        exact ⟨hin_sc ▸ hin_m ▸ rfl, hmk_sc ▸ hm_other x hxu,
          ho_x.2.2.2.2.trans (hd_m ▸ rfl), ho_x.2.1.trans (hch_m ▸ rfl), hk_sc ▸ hk_m ▸ rfl⟩
      · have hx_in_c : x ∈ c.nodes := c.nodes_eq ▸ List.mem_cons_of_mem c.root hx
        have hx_rest : x ∈ forestNodes c_rest := mem_forestNodes_iff.mpr ⟨c, hc_mem, hx_in_c⟩
        have hxu : x ≠ u := fun e => hu_not_other (List.mem_append_left _ (e ▸ hx_rest))
        have ho_x := ho_sc x (List.mem_append_left _ hx_rest)
        exact ⟨ho_x.1.trans (by rw [hpar_m, Function.update_of_ne hxu]),
          ho_x.2.2.1.trans (hl_m ▸ rfl), ho_x.2.2.2.1.trans (hr_m ▸ rfl), Iff.rfl⟩
    have hchain_next : RightChain (RawState.ofData n base a_next).right c_tl := by
      have hch_tl : RightChain st.right c_tl := by
        rcases c_tl with _ | ⟨v, rest⟩
        · trivial
        · exact hchain.2
      rw [hst_next]
      refine hch_tl.frame fun x hx => ?_
      obtain ⟨c, hc_mem, rfl⟩ := List.mem_map.mp (hperm_tl.subset hx)
      have hx_rest : c.root ∈ forestNodes c_rest :=
        mem_forestNodes_iff.mpr ⟨c, hc_mem, c.root_mem_nodes⟩
      exact (ho_sc c.root (List.mem_append_left _ hx_rest)).2.2.2.1.trans (hr_m ▸ rfl)
    have hnm_next :
        (RawState.ofData n base a_next).numMarked =
          markedCount (RawState.ofData n base a_next) := by
      rw [hst_next, hnm_sc, hnm_m]
      exact markedCount_congr fun x => by rw [hin_sc, hmk_sc]
    have hic_next : ∀ v tl, c_tl = v :: tl → a_next.regs iterCur = v.val := by
      intro v tl hv
      subst hv
      have hnxt_eq : nxtVal = v.val := hchain.1
      simp only [a_next, Data.set_regs, Function.update_of_ne (by decide : iterCur ≠ remReg),
        Function.update_self, hnxt_eq]
    obtain ⟨b, slotTrees', maxDeg', t_tl, he_tl, ht_tl, hb_b, hbr_b, hmod_tl, hregs_tl,
      hmd_b, hperm_b, hnd_b, hs_b,
      hk_b, hin_b, hmin_b, hnr_b, hsz_b, hnm_b, hnm_le_b, ho_b⟩ :=
      ih a_next c_rest slotTrees_1 fixedNodes z maxDeg_1 hb_next hbr_next hz_mem hnd_next hs_next
        hsub_next hperm_tl hchain_next
        (by simp only [a_next, Data.set_regs, Function.update_self])
        (by simp only [a_next, Data.set_regs,
              Function.update_of_ne (by decide : maxDegReg ≠ remReg),
              Function.update_of_ne (by decide : maxDegReg ≠ iterCur), hmd_sc])
        hnm_next hic_next
    have he_all : ExecWithin w childScatterLoop a b (t_sc + 13 + t_tl) :=
      (ExecWithin.loop_iter hc he_body he_tl).mono (by omega)
    have hmod_all : Modifies (Block.mk base (space n)).footprint a.mem b.mem :=
      modifies_block_trans (modifies_block_trans (modifies_block_trans hmod1 hmod2) hmod3) hmod_tl
    have hperm_final :
        (forestNodes slotTrees').Perm (forestNodes c_trees ++ forestNodes slotTrees) :=
      hperm_b.trans <| (hperm_sc.append_left _).trans <| (perm_swap_front _ _ _).trans <| by
        rw [← List.append_assoc]
        exact hperm_fn.append_right _
    refine ⟨b, slotTrees', maxDeg', t_sc + 13 + t_tl, he_all,
      by simp only [List.length_cons] at ht_sc ht_tl ⊢; omega,
      hb_b, hbr_b, hmod_all, ?_, hmd_b, hperm_final, hnd_b, hs_b, ?_⟩
    · intro r hr hne_nm
      have ne_rem : r ≠ remReg := fun e => by subst e; change 30 < 30 at hr; omega
      have ne_ic : r ≠ iterCur := fun e => by subst e; change 31 < 30 at hr; omega
      have ne_in : r ≠ iterNxt := fun e => by subst e; change 32 < 30 at hr; omega
      have ne0 : r ≠ s0 := fun e => by subst e; change 35 < 30 at hr; omega
      have ne1 : r ≠ s1 := fun e => by subst e; change 36 < 30 at hr; omega
      rw [hregs_tl r hr hne_nm]
      simp only [a_next, Data.set_regs, Function.update_of_ne ne_rem, Function.update_of_ne ne_ic]
      rw [hlow_sc r (by omega), hregs_mid r ne0 hne_nm]
      simp only [a1, Data.set_regs, Data.write_regs, Function.update_of_ne ne1,
        Function.update_of_ne ne0, Function.update_of_ne ne_in]
    · dsimp only
      rw [hst_next] at hk_b hin_b hmin_b hnr_b hsz_b hnm_le_b ho_b
      refine ⟨hk_b.trans (hk_sc.trans hk_m), hin_b.trans (hin_sc.trans hin_m),
        hmin_b.trans (hmin_sc.trans hmin_m), hnr_b.trans (hnr_sc.trans hnr_m),
        hsz_b.trans (hsz_sc.trans hsz_m), hnm_b,
        hnm_le_b.trans (hnm_sc ▸ hnm_le_m), fun v hv => ?_⟩
      have hvu : v ≠ u := fun e => hu_not_other
        (List.mem_append_right _ (List.mem_append_right _ (e ▸ hv)))
      have pb := ho_b v hv
      have psc := ho_sc v (List.mem_append_right _ hv)
      exact ⟨pb.1.trans (psc.1.trans (by rw [hpar_m, Function.update_of_ne hvu])),
        pb.2.1.trans (psc.2.1.trans (hch_m ▸ rfl)),
        pb.2.2.1.trans (psc.2.2.1.trans (hl_m ▸ rfl)),
        pb.2.2.2.1.trans (psc.2.2.2.1.trans (hr_m ▸ rfl)),
        pb.2.2.2.2.1.trans (psc.2.2.2.2.trans (hd_m ▸ rfl)),
        pb.2.2.2.2.2.trans ((congrFun hmk_sc v).trans (hm_other v hvu))⟩

private abbrev rootScatterBody : Code .exact rFib :=
  ram_exact[
    s0 ← rightBase + iterCur;
    iterNxt ← *s0;
    ⟪scatterRootCode⟫;
    iterCur ← iterNxt;
    remReg ← remReg - oneP
  ]

private abbrev rootScatterLoop : Code .exact rFib :=
  .loop (.lt zeroP remReg) rootScatterBody

/-- Phase A2 loop: scatters each remaining root in `r_trees` along `r_order` into `cons`. -/
private theorem scatterRootsLoop_exec {n base w : ℕ}
    (r_order : List (Fin n)) :
    ∀ (a : Data rFib) (r_trees slotTrees : List (FHTree n)) (fixedNodes : List (Fin n))
      (z : Fin n) (maxDeg : ℕ),
      a.Bounded w → BaseRegs n base a →
      z ∈ fixedNodes →
      (forestNodes r_trees ++ (forestNodes slotTrees ++ fixedNodes)).Nodup →
      SlotInv n (RawState.ofData n base a) slotTrees maxDeg →
      (∀ R ∈ r_trees, ValidRoot (RawState.ofData n base a) none R) →
      r_order.Perm (r_trees.map FHTree.root) →
      RightChain (RawState.ofData n base a).right r_order →
      a.regs remReg = r_order.length →
      a.regs maxDegReg = maxDeg →
      (∀ u tl, r_order = u :: tl → a.regs iterCur = u.val) →
      ∃ b slotTrees' maxDeg' t,
        ExecWithin w rootScatterLoop a b t ∧
        t + slotCredit * slotTrees'.length ≤
          2 + 69 * r_order.length + slotCredit * slotTrees.length ∧
        b.Bounded w ∧ BaseRegs n base b ∧
        Modifies (Block.mk base (space n)).footprint a.mem b.mem ∧
        (∀ r : Fin rFib, r.val < 30 → b.regs r = a.regs r) ∧
        b.regs maxDegReg = maxDeg' ∧
        (forestNodes slotTrees').Perm (forestNodes r_trees ++ forestNodes slotTrees) ∧
        (forestNodes slotTrees' ++ fixedNodes).Nodup ∧
        SlotInv n (RawState.ofData n base b) slotTrees' maxDeg' ∧
        (let st := RawState.ofData n base a
         let st' := RawState.ofData n base b
         st'.key = st.key ∧ st'.mark = st.mark ∧ st'.inHeap = st.inHeap ∧
         st'.minRoot = st.minRoot ∧ st'.numRoots = st.numRoots ∧
         st'.numMarked = st.numMarked ∧ st'.sz = st.sz ∧
         ∀ v ∈ fixedNodes,
           st'.par v = st.par v ∧ st'.child v = st.child v ∧
           st'.left v = st.left v ∧ st'.right v = st.right v ∧ st'.deg v = st.deg v) := by
  induction r_order with
  | nil =>
    intro a r_trees slotTrees fixedNodes _ maxDeg hb hbr _ hnd hs _ hperm _ hrem hmd _
    have hz0 : a.regs zeroP = 0 := hbr.2.2.2.2.2.2.2.2.2.2.2.1
    have hc : ¬(Cond.lt zeroP remReg).Holds a := by
      simp only [Cond.Holds, hz0, hrem, List.length_nil, Nat.lt_irrefl, not_false_eq_true]
    have hrt_nil : r_trees = [] := by
      apply List.eq_nil_of_length_eq_zero
      have hlen := hperm.length_eq
      simp only [List.length_nil, List.length_map] at hlen
      omega
    subst hrt_nil
    exact ⟨a, slotTrees, maxDeg, 2, ExecWithin.loop_exit hc, by omega, hb, hbr,
      Modifies.refl _ _, fun _ _ => rfl, hmd,
      by simp only [forestNodes, List.nil_append, List.Perm.refl],
      by simpa only [forestNodes, List.nil_append] using hnd,
      hs, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl⟩⟩⟩
  | cons u r_tl ih =>
    intro a r_trees slotTrees fixedNodes z maxDeg hb hbr hz_mem hnd hs hroots hperm hchain hrem
      hmd hic
    set st := RawState.ofData n base a with hst_def
    have hfit_stop := hbr.fits_stop hb
    have hz0 : a.regs zeroP = 0 := hbr.2.2.2.2.2.2.2.2.2.2.2.1
    have hrb : a.regs rightBase = base + 4 * n := hbr.2.2.2.2.2.2.1
    have hc : (Cond.lt zeroP remReg).Holds a := by
      simp only [Cond.Holds, hz0, hrem, List.length_cons]; omega
    have hu_ic : a.regs iterCur = u.val := hic u r_tl rfl
    have hnd_r : (forestNodes r_trees).Nodup := (List.nodup_append.mp hnd).1
    obtain ⟨idx, hidx, hTu_root, hperm_tl, hperm_fn⟩ := extract_tree_by_root hnd_r hperm
    let T_u := r_trees[idx]
    let r_rest := r_trees.eraseIdx idx
    have hTu_valid : ValidRoot st none T_u := hroots T_u (List.getElem_mem hidx)
    have hnd_split :
        ((T_u.nodes ++ forestNodes r_rest) ++ (forestNodes slotTrees ++ fixedNodes)).Nodup :=
      (hperm_fn.append_right _).nodup_iff.mpr hnd
    have hnd_for_sc :
        (T_u.nodes ++ (forestNodes slotTrees ++ (forestNodes r_rest ++ fixedNodes))).Nodup :=
      (perm_reassoc_mid T_u.nodes (forestNodes r_rest) (forestNodes slotTrees)
        fixedNodes).nodup_iff.mpr hnd_split
    -- Step 1 (`a → a1`, 2 steps): `s0 ← rightBase + iterCur; iterNxt ← *s0`
    let nxtVal := st.right u
    let a1 := (a.set s0 (base + 4 * n + u.val)).set iterNxt nxtVal
    have s1_1 : ExecWithin w (.op (.exactBin .add s0 rightBase iterCur)) a
        (a.set s0 (base + 4 * n + u.val)) 1 := by
      have := u.isLt
      simpa only [hrb, hu_ic] using
        execWithin_exactAdd (x := a) (d := s0) (i := rightBase) (j := iterCur)
          (by rw [hrb, hu_ic]; exact hfit_stop.of_le (by simp only [space]; omega))
    have s1_2 : ExecWithin (B := .exact) w (.op (.load iterNxt s0))
        (a.set s0 (base + 4 * n + u.val)) a1 1 := by
      have hm_r : a.mem (base + 4 * n + u.val) = nxtVal := rfl
      simpa only [a1, Data.set_mem, Data.set_regs, Function.update_self, hm_r] using
        (ExecWithin.load (B := .exact) (w := w) (x := a.set s0 (base + 4 * n + u.val))
          (d := iterNxt) (a := s0))
    have hb1 : a1.Bounded w := s1_2.bounded (s1_1.bounded hb)
    have hbr1 : BaseRegs n base a1 :=
      (hbr.set_non_base (by decide) _).set_non_base (by decide) _
    have hst1 : RawState.ofData n base a1 = st := by
      simp only [a1, ofData_set_scratch _ (by decide : 17 ≤ iterNxt.val),
        ofData_set_scratch _ (by decide : 17 ≤ s0.val), ← hst_def]
    -- Step 2 (`a1 → a_sc`, `t_sc` steps): `scatterRootCode` on `T_u`
    have hTu_r : T_u.root = u := hTu_root
    obtain ⟨a_sc, slotTrees_1, maxDeg_1, t_sc, he2, ht_sc, hb_sc, hbr_sc, hmod2, hlow_sc,
      hmd_sc, hperm_sc, hnd_sc, hs_sc,
      hk_sc, hmk_sc, hin_sc, hmin_sc, hnr_sc, hnm_sc, hsz_sc, ho_sc⟩ :=
      scatterRootCode_exec hb1 hbr1 (List.mem_append_right _ hz_mem)
        hnd_for_sc (by rw [hst1]; exact hs) (by rw [hst1]; exact hTu_valid)
        (by simp only [a1, Data.set_regs, Function.update_of_ne (by decide : iterCur ≠ iterNxt),
              Function.update_of_ne (by decide : iterCur ≠ s0), hu_ic, hTu_r])
        (by simp only [a1, Data.set_regs, Function.update_of_ne (by decide : maxDegReg ≠ iterNxt),
              Function.update_of_ne (by decide : maxDegReg ≠ s0), hmd])
    -- Step 3 (`a_sc → a_next`, 2 steps): `iterCur ← iterNxt; remReg ← remReg - oneP`
    have hsc_nxt : a_sc.regs iterNxt = nxtVal := by
      rw [hlow_sc iterNxt (by decide)]
      simp only [a1, Data.set_regs, Function.update_self]
    have hsc_rem : a_sc.regs remReg = r_tl.length + 1 := by
      rw [hlow_sc remReg (by decide)]
      simp only [a1, Data.set_regs, Function.update_of_ne (by decide : remReg ≠ iterNxt),
        Function.update_of_ne (by decide : remReg ≠ s0), hrem, List.length_cons]
    let a_next := (a_sc.set iterCur nxtVal).set remReg r_tl.length
    have s3_1 : ExecWithin (B := .exact) w (.op (.copy iterCur iterNxt)) a_sc
        (a_sc.set iterCur nxtVal) 1 := by
      simpa only [hsc_nxt] using
        (ExecWithin.copy (B := .exact) (w := w) (x := a_sc) (d := iterCur) (s := iterNxt))
    have s3_2 : ExecWithin w (.op (.exactBin .sub remReg remReg oneP))
        (a_sc.set iterCur nxtVal) a_next 1 := by
      have hrem_w : (a_sc.set iterCur nxtVal).regs remReg = r_tl.length + 1 := hsc_rem
      have ho1_w : (a_sc.set iterCur nxtVal).regs oneP = 1 := hbr_sc.2.2.2.2.2.2.2.2.2.2.2.2
      simpa only [hrem_w, ho1_w, Nat.add_sub_cancel] using
        execWithin_exactSub (x := a_sc.set iterCur nxtVal) (d := remReg) (i := remReg) (j := oneP)
          (by rw [hrem_w, ho1_w]; omega)
          (by rw [hrem_w, ho1_w]; exact (hb_sc.1 remReg).of_le (by omega))
    have he_body : ExecWithin w rootScatterBody a a_next (t_sc + 4) := by
      unfold rootScatterBody
      exact (s1_1.seq <| s1_2.seq <| he2.seq <| s3_1.seq s3_2).mono (by omega)
    have hb_next : a_next.Bounded w := s3_2.bounded (s3_1.bounded hb_sc)
    have hbr_next : BaseRegs n base a_next :=
      (hbr_sc.set_non_base (by decide) _).set_non_base (by decide) _
    have hst_next : RawState.ofData n base a_next = RawState.ofData n base a_sc := by
      simp only [a_next, ofData_set_scratch _ (by decide : 17 ≤ remReg.val),
        ofData_set_scratch _ (by decide : 17 ≤ iterCur.val)]
    have hnd_next : (forestNodes r_rest ++ (forestNodes slotTrees_1 ++ fixedNodes)).Nodup :=
      (perm_swap_front (forestNodes slotTrees_1) (forestNodes r_rest) fixedNodes).nodup_iff.mp
        hnd_sc
    have hroots_next : ∀ R ∈ r_rest, ValidRoot (RawState.ofData n base a_next) none R := by
      intro R hR_mem
      obtain ⟨j, hj, _, hR_eq⟩ := List.mem_eraseIdx_iff_getElem.mp hR_mem
      have hR_val : ValidRoot st none R := hR_eq ▸ hroots _ (List.getElem_mem hj)
      rw [hst_next]
      refine hR_val.frame_nodes fun x hx => ?_
      have hx_rest : x ∈ forestNodes r_rest := mem_forestNodes_iff.mpr ⟨R, hR_mem, hx⟩
      have ho_x := ho_sc x (List.mem_append_left _ hx_rest)
      rw [hst1] at hin_sc hmk_sc hk_sc ho_x
      exact ⟨hin_sc ▸ rfl, hmk_sc ▸ rfl, ho_x.2.2.2.2, ho_x.2.1, hk_sc ▸ rfl, ho_x.1,
        ho_x.2.2.1, ho_x.2.2.2.1⟩
    have hchain_next : RightChain (RawState.ofData n base a_next).right r_tl := by
      have hch_tl : RightChain st.right r_tl := by
        rcases r_tl with _ | ⟨v, rest⟩
        · trivial
        · exact hchain.2
      rw [hst_next]
      refine hch_tl.frame fun x hx => ?_
      obtain ⟨R, hR_mem, rfl⟩ := List.mem_map.mp (hperm_tl.subset hx)
      have hx_rest : R.root ∈ forestNodes r_rest :=
        mem_forestNodes_iff.mpr ⟨R, hR_mem, R.root_mem_nodes⟩
      have ho_x := ho_sc R.root (List.mem_append_left _ hx_rest)
      rw [hst1] at ho_x
      exact ho_x.2.2.2.1
    have hic_next : ∀ v tl, r_tl = v :: tl → a_next.regs iterCur = v.val := by
      intro v tl hv
      subst hv
      have hnxt_eq : nxtVal = v.val := hchain.1
      simp only [a_next, Data.set_regs, Function.update_of_ne (by decide : iterCur ≠ remReg),
        Function.update_self, hnxt_eq]
    obtain ⟨b, slotTrees', maxDeg', t_tl, he_tl, ht_tl, hb_b, hbr_b, hmod_tl, hregs_tl,
      hmd_b, hperm_b, hnd_b, hs_b,
      hk_b, hmk_b, hin_b, hmin_b, hnr_b, hnm_b, hsz_b, ho_b⟩ :=
      ih a_next r_rest slotTrees_1 fixedNodes z maxDeg_1 hb_next hbr_next hz_mem hnd_next
        (by rw [hst_next]; exact hs_sc) hroots_next hperm_tl hchain_next
        (by simp only [a_next, Data.set_regs, Function.update_self])
        (by simp only [a_next, Data.set_regs,
              Function.update_of_ne (by decide : maxDegReg ≠ remReg),
              Function.update_of_ne (by decide : maxDegReg ≠ iterCur), hmd_sc])
        hic_next
    have he_all : ExecWithin w rootScatterLoop a b (t_sc + 6 + t_tl) :=
      (ExecWithin.loop_iter hc he_body he_tl).mono (by omega)
    have hmod_all : Modifies (Block.mk base (space n)).footprint a.mem b.mem :=
      modifies_block_trans hmod2 hmod_tl
    have hperm_final :
        (forestNodes slotTrees').Perm (forestNodes r_trees ++ forestNodes slotTrees) :=
      hperm_b.trans <| (hperm_sc.append_left _).trans <| (perm_swap_front _ _ _).trans <| by
        rw [← List.append_assoc]
        exact hperm_fn.append_right _
    refine ⟨b, slotTrees', maxDeg', t_sc + 6 + t_tl, he_all,
      by simp only [List.length_cons] at ht_sc ht_tl ⊢; omega,
      hb_b, hbr_b, hmod_all, ?_, hmd_b, hperm_final, hnd_b, hs_b, ?_⟩
    · intro r hr
      have ne_rem : r ≠ remReg := fun e => by subst e; change 30 < 30 at hr; omega
      have ne_ic : r ≠ iterCur := fun e => by subst e; change 31 < 30 at hr; omega
      have ne_in : r ≠ iterNxt := fun e => by subst e; change 32 < 30 at hr; omega
      have ne0 : r ≠ s0 := fun e => by subst e; change 35 < 30 at hr; omega
      rw [hregs_tl r hr]
      simp only [a_next, Data.set_regs, Function.update_of_ne ne_rem, Function.update_of_ne ne_ic]
      rw [hlow_sc r (by omega)]
      simp only [a1, Data.set_regs, Function.update_of_ne ne_in, Function.update_of_ne ne0]
    · dsimp only
      rw [hst_next] at hk_b hmk_b hin_b hmin_b hnr_b hnm_b hsz_b ho_b
      rw [hst1] at hk_sc hmk_sc hin_sc hmin_sc hnr_sc hnm_sc hsz_sc ho_sc
      refine ⟨hk_b.trans hk_sc, hmk_b.trans hmk_sc, hin_b.trans hin_sc,
        hmin_b.trans hmin_sc, hnr_b.trans hnr_sc, hnm_b.trans hnm_sc, hsz_b.trans hsz_sc,
        fun v hv => ?_⟩
      have pb := ho_b v hv
      have psc := ho_sc v (List.mem_append_right _ hv)
      exact ⟨pb.1.trans psc.1, pb.2.1.trans psc.2.1, pb.2.2.1.trans psc.2.2.1,
        pb.2.2.2.1.trans psc.2.2.2.1, pb.2.2.2.2.trans psc.2.2.2.2⟩

/-! ## Phase B slot gathering (`gatherSlotsLoop_exec`) -/

private theorem perm_move_to_acc {α : Type*} (X R : List α) (z : α) (A : List α) :
    ((X ++ R) ++ (z :: A)).Perm (R ++ (z :: (X ++ A))) := by
  rw [List.append_assoc]
  refine List.perm_append_comm.trans ?_
  rw [List.append_assoc, List.cons_append]
  exact (List.Perm.cons z List.perm_append_comm).append_left R

private def NoStore : Code .exact rFib → Bool
  | .op (.store _ _) => false
  | .op _ => true
  | .seq c₁ c₂ => NoStore c₁ && NoStore c₂
  | .branch _ c₁ c₂ => NoStore c₁ && NoStore c₂
  | .loop _ b => NoStore b
  | .rand _ _ => true

private theorem mem_eq_of_noStore {w t : ℕ} {c : Code .exact rFib} {x y : Data rFib}
    (he : Exec w c x y t) (hns : NoStore c = true) : y.mem = x.mem := by
  induction he with
  | op ho =>
    rename_i o _ _
    cases o with
    | const _ _ => obtain ⟨_, rfl⟩ := Data.put_eq_some.mp ho; rfl
    | copy _ _ => cases ho; rfl
    | load _ _ => cases ho; rfl
    | alu _ _ _ => obtain ⟨_, _, _, rfl⟩ := Op.eval_alu_eq_some.mp ho; rfl
    | store _ _ => simp only [NoStore, Bool.false_eq_true] at hns
  | seq _ _ ih₁ ih₂ =>
    obtain ⟨h₁, h₂⟩ := Bool.and_eq_true_iff.mp hns
    exact (ih₂ h₂).trans (ih₁ h₁)
  | branch_pos _ _ ih => exact ih (Bool.and_eq_true_iff.mp hns).1
  | branch_neg _ _ ih => exact ih (Bool.and_eq_true_iff.mp hns).2
  | loop_exit _ => rfl
  | loop_iter _ _ _ ihb ihl => exact (ihl hns).trans (ihb hns)

/-- `addRootAndUpdateMin iterCur` modifies `left` and `right` only at roots in `T_u :: ts`. -/
private theorem addRootIterCur_lr_frame {n base w : ℕ} {x y : Data rFib}
    (hb : x.Bounded w) (hbr : BaseRegs n base x)
    {u : Fin n} (hu_val : x.regs iterCur = u.val)
    {T_u : FHTree n} {ts : List (FHTree n)}
    (hu_root : T_u.root = u)
    (hnd : (forestNodes (T_u :: ts)).Nodup)
    (hrl : (ts = [] ∧ (RawState.ofData n base x).minRoot = 0) ∨
      ∃ (m : Fin n) (rtail : List (Fin n)),
        (RawState.ofData n base x).minRoot = m.val + 1 ∧
        IsCircList (RawState.ofData n base x).left (RawState.ofData n base x).right (m :: rtail) ∧
        (m :: rtail).Perm (ts.map FHTree.root) ∧
        ∀ T ∈ ts, IndexedMinPQ.PrioLE
          (m, (RawState.ofData n base x).key m)
          (T.root, (RawState.ofData n base x).key T.root))
    (he : ExecWithin w (addRootAndUpdateMin iterCur) x y 28) :
    ∀ v ∉ (T_u :: ts).map FHTree.root,
      (RawState.ofData n base y).left v = (RawState.ofData n base x).left v ∧
      (RawState.ofData n base y).right v = (RawState.ofData n base x).right v := by
  have hfit_stop := hbr.fits_stop hb
  have hz0 : x.regs zeroP = 0 := hbr.2.2.2.2.2.2.2.2.2.2.2.1
  have ho1 : x.regs oneP = 1 := hbr.2.2.2.2.2.2.2.2.2.2.2.2
  have hu_lt := u.isLt
  obtain ⟨_, _, he_ex⟩ := he
  unfold addRootAndUpdateMin at he_ex
  cases he_ex with
  | seq hb_ex hinc_ex =>
    have hm_inc : y.mem = _ := mem_eq_of_noStore hinc_ex (by decide)
    rcases hrl with ⟨rfl, hmin0⟩ | ⟨m, rtail, hmin_m, hcirc, hperm, _⟩
    · have hc : (Cond.eq minRootReg zeroP).Holds x := by
        simp only [Cond.Holds, hz0]; exact hmin0
      cases hb_ex with
      | branch_neg hc' _ => exact absurd hc hc'
      | branch_pos _ hp_ex =>
        have hl_base : x.regs leftBase = base + 3 * n := hbr.2.2.2.2.2.1
        have hr_base : x.regs rightBase = base + 4 * n := hbr.2.2.2.2.2.2.1
        let x1 := (x.set s0 (base + 3 * n + u.val)).write (base + 3 * n + u.val) u.val
        let x2 := (x1.set s0 (base + 4 * n + u.val)).write (base + 4 * n + u.val) u.val
        let x3 := x2.set minRootReg (u.val + 1)
        have s1_add : ExecWithin w (.op (.exactBin .add s0 leftBase iterCur)) x
            (x.set s0 (base + 3 * n + u.val)) 1 := by
          simpa only [hl_base, hu_val] using
            execWithin_exactAdd (x := x) (d := s0) (i := leftBase) (j := iterCur)
              (by rw [hl_base, hu_val]; exact hfit_stop.of_le (by simp only [space]; omega))
        have s2_st : ExecWithin (B := .exact) w (.op (.store s0 iterCur))
            (x.set s0 (base + 3 * n + u.val)) x1 1 := by
          simpa only [Data.set_regs, Function.update_self,
            Function.update_of_ne (by decide : iterCur ≠ s0), hu_val] using
            (ExecWithin.store (B := .exact) (w := w) (x := x.set s0 (base + 3 * n + u.val))
              (a := s0) (s := iterCur))
        have hx1_r : x1.regs rightBase = base + 4 * n := by
          simp only [x1, Data.write_regs, Data.set_regs,
            Function.update_of_ne (by decide : rightBase ≠ s0), hr_base]
        have hx1_u : x1.regs iterCur = u.val := by
          simp only [x1, Data.write_regs, Data.set_regs,
            Function.update_of_ne (by decide : iterCur ≠ s0), hu_val]
        have s3_add : ExecWithin w (.op (.exactBin .add s0 rightBase iterCur)) x1
            (x1.set s0 (base + 4 * n + u.val)) 1 := by
          simpa only [hx1_r, hx1_u] using
            execWithin_exactAdd (x := x1) (d := s0) (i := rightBase) (j := iterCur)
              (by rw [hx1_r, hx1_u]; exact hfit_stop.of_le (by simp only [space]; omega))
        have s4_st : ExecWithin (B := .exact) w (.op (.store s0 iterCur))
            (x1.set s0 (base + 4 * n + u.val)) x2 1 := by
          simpa only [Data.set_regs, Function.update_self,
            Function.update_of_ne (by decide : iterCur ≠ s0), hx1_u] using
            (ExecWithin.store (B := .exact) (w := w) (x := x1.set s0 (base + 4 * n + u.val))
              (a := s0) (s := iterCur))
        have hx2_u : x2.regs iterCur = u.val := by
          simp only [x2, Data.write_regs, Data.set_regs,
            Function.update_of_ne (by decide : iterCur ≠ s0), hx1_u]
        have hx2_one : x2.regs oneP = 1 := by
          simp only [x2, x1, Data.write_regs, Data.set_regs,
            Function.update_of_ne (by decide : oneP ≠ s0), ho1]
        have s5_add : ExecWithin w (.op (.exactBin .add minRootReg iterCur oneP)) x2 x3 1 := by
          simpa only [hx2_u, hx2_one] using
            execWithin_exactAdd (x := x2) (d := minRootReg) (i := iterCur) (j := oneP)
              (by rw [hx2_u, hx2_one]; exact hfit_stop.of_le (by simp only [space]; omega))
        obtain ⟨_, _, hp_ex'⟩ := s1_add.seq (s2_st.seq (s3_add.seq (s4_st.seq s5_add)))
        obtain ⟨rfl, _⟩ := hp_ex.unique hp_ex'
        have hst3 : RawState.ofData n base x3 =
            { RawState.ofData n base x with
              left := Function.update (RawState.ofData n base x).left u u.val
              right := Function.update (RawState.ofData n base x).right u u.val
              minRoot := u.val + 1 } := by
          simp only [x3, x2, x1, ofData_set_minRoot, ofData_write_right, ofData_write_left,
            ofData_set_scratch _ (by decide : 17 ≤ s0.val)]
        have hl_eq : (RawState.ofData n base y).left = (RawState.ofData n base x3).left := by
          funext w'; change y.mem _ = x3.mem _; rw [hm_inc]
        have hr_eq : (RawState.ofData n base y).right = (RawState.ofData n base x3).right := by
          funext w'; change y.mem _ = x3.mem _; rw [hm_inc]
        intro v hv
        have hvu : v ≠ u := fun e => hv (by simp only [List.map, hu_root, e, List.mem_singleton])
        rw [hl_eq, hr_eq, hst3]
        exact ⟨Function.update_of_ne hvu _ _, Function.update_of_ne hvu _ _⟩
    · have hc : ¬(Cond.eq minRootReg zeroP).Holds x := by
        simp only [Cond.Holds, hz0]
        change (RawState.ofData n base x).minRoot ≠ 0
        rw [hmin_m]
        exact Nat.succ_ne_zero m.val
      cases hb_ex with
      | branch_pos hc' _ => exact absurd hc' hc
      | branch_neg _ hn_ex =>
        cases hn_ex with
        | seq hs1 hn_rest =>
          cases hn_rest with
          | seq hins_ex htail_ex =>
            let x1 := x.set s1 m.val
            have he_sub : ExecWithin w (.op (.exactBin .sub s1 minRootReg oneP)) x x1 1 := by
              have hmin_x : x.regs minRootReg = m.val + 1 := hmin_m
              have hm_lt := m.isLt
              simpa only [hmin_x, ho1, Nat.add_sub_cancel] using
                execWithin_exactSub (x := x) (d := s1) (i := minRootReg) (j := oneP)
                  (by rw [hmin_x, ho1]; omega)
                  (by rw [hmin_x, ho1]; exact hfit_stop.of_le (by simp only [space]; omega))
            have hb1 : x1.Bounded w := he_sub.bounded hb
            obtain ⟨_, _, hs1'⟩ := he_sub
            obtain ⟨rfl, _⟩ := hs1.unique hs1'
            have hbr1 : BaseRegs n base x1 := hbr.set_non_base (by decide) m.val
            have hst1 : RawState.ofData n base x1 = RawState.ofData n base x :=
              ofData_set_scratch x (by decide : 17 ≤ s1.val) m.val
            have hu_not_roots : u ∉ m :: rtail := by
              intro hm_in
              obtain ⟨R, hR, hR_root⟩ := List.mem_map.mp (hperm.subset hm_in)
              have hnd_cons := List.nodup_append.mp hnd
              exact hnd_cons.2.2 u (hu_root ▸ T_u.root_mem_nodes) u
                (mem_forestNodes_iff.mpr ⟨R, hR, hR_root ▸ R.root_mem_nodes⟩) rfl
            have hx1_s1 : x1.regs s1 = m.val := by
              simp only [x1, Data.set_regs, Function.update_self]
            have hx1_u : x1.regs iterCur = u.val := by
              simp only [x1, Data.set_regs,
                Function.update_of_ne (by decide : iterCur ≠ s1), hu_val]
            obtain ⟨x2, ⟨_, _, hins'⟩, _, _, ⟨r, _, hr_mem, hst2⟩, _⟩ :=
              insertIntoNonEmptyList_exec hb1 hbr1 (by decide) (by decide) (by decide) (by decide)
                hx1_s1 hx1_u (hst1 ▸ hcirc) hu_not_roots
            obtain ⟨hx2_eq, _⟩ := hins_ex.unique hins'
            rw [hx2_eq] at htail_ex
            rw [hst1] at hst2
            have hm_tail := mem_eq_of_noStore htail_ex (by decide)
            have hl_eq : (RawState.ofData n base y).left = (RawState.ofData n base x2).left := by
              funext w'; change y.mem _ = x2.mem _; rw [hm_inc, hm_tail]
            have hr_eq : (RawState.ofData n base y).right = (RawState.ofData n base x2).right := by
              funext w'; change y.mem _ = x2.mem _; rw [hm_inc, hm_tail]
            intro v hv
            have hvu : v ≠ u := fun e =>
              hv (by simp only [List.map_cons, hu_root, e, List.mem_cons_self])
            have hvm : v ≠ m := fun e =>
              hv (List.mem_cons_of_mem _ (e ▸ hperm.subset List.mem_cons_self))
            have hvr : v ≠ r := fun e =>
              hv (List.mem_cons_of_mem _ (e ▸ hperm.subset hr_mem))
            rw [hl_eq, hr_eq, hst2]
            simp only [Function.update_of_ne hvr, Function.update_of_ne hvu,
              Function.update_of_ne hvm]
            exact ⟨trivial, trivial⟩

private abbrev gatherSlotBody : Code .exact rFib :=
  ram_exact[
    s0 ← consBase + curDReg;
    s3 ← *s0;
    if zeroP < s3 then [
      *s0 ← zeroP;
      iterCur ← s3 - oneP;
      ⟪addRootAndUpdateMin iterCur⟫
    ] else [
      s0 ← zeroP
    ];
    curDReg ← curDReg + oneP
  ]

private abbrev gatherSlotsLoop : Code .exact rFib :=
  .loop (.lt curDReg maxDegReg) gatherSlotBody

/-- Phase B loop: scans `curD` up to `maxDeg + 1` (`curD + rem = maxDeg + 1`), clearing every
occupied `cons[curD]` and splicing its consolidated root into `accRoots` via
`addRootAndUpdateMin iterCur`. -/
private theorem gatherSlotsLoop_exec {n base w maxDeg : ℕ} (hn_pos : 1 ≤ n)
    (rem : ℕ) :
    ∀ (a : Data rFib) (curD : ℕ) (slotTrees accRoots : List (FHTree n)) (z : Fin n),
      curD + rem = maxDeg + 1 →
      a.Bounded w → BaseRegs n base a →
      a.regs curDReg = curD →
      a.regs maxDegReg = maxDeg + 1 →
      SlotInv n (RawState.ofData n base a) slotTrees maxDeg →
      (∀ d < curD, ∀ T ∈ slotTrees, T.deg ≠ d) →
      (forestNodes slotTrees ++ (z :: forestNodes accRoots)).Nodup →
      (∀ T ∈ accRoots, ValidRoot (RawState.ofData n base a) none T) →
      (RawState.ofData n base a).numRoots = accRoots.length →
      ((accRoots = [] ∧ (RawState.ofData n base a).minRoot = 0) ∨
        ∃ (m : Fin n) (rtail : List (Fin n)),
          (RawState.ofData n base a).minRoot = m.val + 1 ∧
          IsCircList (RawState.ofData n base a).left (RawState.ofData n base a).right (m :: rtail) ∧
          (m :: rtail).Perm (accRoots.map FHTree.root) ∧
          ∀ T ∈ accRoots, IndexedMinPQ.PrioLE
            (m, (RawState.ofData n base a).key m)
            (T.root, (RawState.ofData n base a).key T.root)) →
      ∃ b finalRoots t,
        ExecWithin w gatherSlotsLoop a b t ∧
        t + unitCredit * finalRoots.length ≤
          2 + 116 * rem + unitCredit * accRoots.length ∧
        b.Bounded w ∧ BaseRegs n base b ∧
        Modifies (Block.mk base (space n)).footprint a.mem b.mem ∧
        (∀ r : Fin rFib, r.val < 30 → r ≠ minRootReg → r ≠ numRootsReg → b.regs r = a.regs r) ∧
        (forestNodes finalRoots).Perm (forestNodes slotTrees ++ forestNodes accRoots) ∧
        (z :: forestNodes finalRoots).Nodup ∧
        (let st := RawState.ofData n base a
         let st' := RawState.ofData n base b
         st'.key = st.key ∧ st'.par = st.par ∧ st'.child = st.child ∧
         st'.deg = st.deg ∧ st'.mark = st.mark ∧ st'.inHeap = st.inHeap ∧
         st'.numMarked = st.numMarked ∧ st'.sz = st.sz ∧
         (∀ d ≤ n, st'.cons d = 0) ∧
         st'.numRoots = finalRoots.length ∧
         (∀ T ∈ finalRoots, ValidRoot st' none T) ∧
         ((finalRoots = [] ∧ st'.minRoot = 0) ∨
           ∃ (m : Fin n) (rtail : List (Fin n)),
             st'.minRoot = m.val + 1 ∧
             IsCircList st'.left st'.right (m :: rtail) ∧
             (m :: rtail).Perm (finalRoots.map FHTree.root) ∧
             ∀ T ∈ finalRoots, IndexedMinPQ.PrioLE (m, st'.key m) (T.root, st'.key T.root))) := by
  induction rem with
  | zero =>
    intro a curD slotTrees accRoots z hsum hb hbr hcurD hmaxD hs hcleared hnd hacc hnr hrl
    have hcur_eq : curD = maxDeg + 1 := by omega
    subst hcur_eq
    have hc : ¬(Cond.lt curDReg maxDegReg).Holds a := by
      simp only [Cond.Holds, hcurD, hmaxD, Nat.lt_irrefl, not_false_eq_true]
    obtain ⟨hnil, hcons0⟩ := hs.done_of_cleared hcleared
    subst hnil
    exact ⟨a, accRoots, 2, ExecWithin.loop_exit hc, by omega, hb, hbr,
      Modifies.refl _ _, fun _ _ _ _ => rfl,
      by simp only [forestNodes, List.nil_append, List.Perm.refl],
      by simpa only [forestNodes, List.nil_append] using hnd,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hcons0, hnr, hacc, hrl⟩⟩
  | succ rem' ih =>
    intro a curD slotTrees accRoots z hsum hb hbr hcurD hmaxD hs hcleared hnd hacc hnr hrl
    set st := RawState.ofData n base a with hst_def
    have hfit_stop := hbr.fits_stop hb
    have hz0 : a.regs zeroP = 0 := hbr.2.2.2.2.2.2.2.2.2.2.2.1
    have ho1 : a.regs oneP = 1 := hbr.2.2.2.2.2.2.2.2.2.2.2.2
    have hconsb : a.regs consBase = base + 8 * n := hbr.2.2.2.2.2.2.2.2.2.2.1
    have hmd_le_n : maxDeg + 1 ≤ n := by
      rcases hs.2.2.2.2.2 with h0 | h2 <;> omega
    have hd_le_n : curD ≤ n := by omega
    have hc_loop : (Cond.lt curDReg maxDegReg).Holds a := by
      simp only [Cond.Holds, hcurD, hmaxD]; omega
    -- Load `s0 ← consBase + curDReg; s3 ← *s0` (2 steps)
    let a1 := (a.set s0 (base + 8 * n + curD)).set s3 (st.cons curD)
    have s_add0 : ExecWithin w (.op (.exactBin .add s0 consBase curDReg)) a
        (a.set s0 (base + 8 * n + curD)) 1 := by
      simpa only [hconsb, hcurD] using
        execWithin_exactAdd (x := a) (d := s0) (i := consBase) (j := curDReg)
          (by rw [hconsb, hcurD]; exact hfit_stop.of_le (by simp only [space]; omega))
    have s_ld0 : ExecWithin (B := .exact) w (.op (.load s3 s0))
        (a.set s0 (base + 8 * n + curD)) a1 1 := by
      have hm_c : a.mem (base + 8 * n + curD) = st.cons curD := by
        change a.mem _ = if curD ≤ n then a.mem _ else 0
        simp only [hd_le_n, ↓reduceIte]
      simpa only [a1, Data.set_mem, Data.set_regs, Function.update_self, hm_c] using
        (ExecWithin.load (B := .exact) (w := w) (x := a.set s0 (base + 8 * n + curD))
          (d := s3) (a := s0))
    have hb1 : a1.Bounded w := s_ld0.bounded (s_add0.bounded hb)
    have hbr1 : BaseRegs n base a1 :=
      (hbr.set_non_base (by decide) _).set_non_base (by decide) _
    have hst1 : RawState.ofData n base a1 = st := by
      simp only [a1, ofData_set_scratch _ (by decide : 17 ≤ s3.val),
        ofData_set_scratch _ (by decide : 17 ≤ s0.val), hst_def]
    have ha1_s0 : a1.regs s0 = base + 8 * n + curD := by
      simp only [a1, Data.set_regs, Function.update_of_ne (by decide : s0 ≠ s3),
        Function.update_self]
    have ha1_s3 : a1.regs s3 = st.cons curD := by
      simp only [a1, Data.set_regs, Function.update_self]
    rcases hs.lookup hd_le_n with ⟨hc0, hnone⟩ |
        ⟨idx, hidx, hslot_deg, hcons_eq, _, hno_other⟩
    · -- Unoccupied slot (`st.cons curD = 0`)
      have hc_br : ¬(Cond.lt zeroP s3).Holds a1 := by
        simp only [Cond.Holds, hbr1.2.2.2.2.2.2.2.2.2.2.2.1, ha1_s3, hc0, Nat.lt_irrefl,
          not_false_eq_true]
      let a2 := a1.set s0 0
      let a3 := a2.set curDReg (curD + 1)
      have he_br : ExecWithin (B := .exact) w
          (.branch (.lt zeroP s3)
            (.seq (.op (.store s0 zeroP)) <|
             .seq (.op (.exactBin .sub iterCur s3 oneP)) (addRootAndUpdateMin iterCur))
            (.op (.copy s0 zeroP))) a1 a2 3 :=
        ExecWithin.branch_neg hc_br (by
          simpa only [hbr1.2.2.2.2.2.2.2.2.2.2.2.1] using
            (ExecWithin.copy (B := .exact) (w := w) (x := a1) (d := s0) (s := zeroP)))
      have ha2_curD : a2.regs curDReg = curD := by
        simp only [a2, a1, Data.set_regs, Function.update_of_ne (by decide : curDReg ≠ s0),
          Function.update_of_ne (by decide : curDReg ≠ s3), hcurD]
      have ha2_o1 : a2.regs oneP = 1 := by
        simp only [a2, a1, Data.set_regs, Function.update_of_ne (by decide : oneP ≠ s0),
          Function.update_of_ne (by decide : oneP ≠ s3), ho1]
      have he_inc : ExecWithin w (.op (.exactBin .add curDReg curDReg oneP)) a2 a3 1 := by
        simpa only [ha2_curD, ha2_o1] using
          execWithin_exactAdd (x := a2) (d := curDReg) (i := curDReg) (j := oneP)
            (by rw [ha2_curD, ha2_o1]; exact hfit_stop.of_le (by simp only [space]; omega))
      have he_body : ExecWithin w gatherSlotBody a a3 6 := by
        unfold gatherSlotBody
        exact (s_add0.seq <| s_ld0.seq <| he_br.seq he_inc).mono (by omega)
      have hb3 : a3.Bounded w := he_inc.bounded (he_br.bounded hb1)
      have hbr3 : BaseRegs n base a3 :=
        (hbr1.set_non_base (by decide) _).set_non_base (by decide) _
      have hst3 : RawState.ofData n base a3 = st := by
        simp only [a3, a2, ofData_set_scratch _ (by decide : 17 ≤ curDReg.val),
          ofData_set_scratch _ (by decide : 17 ≤ s0.val), hst1]
      have hcleared3 : ∀ d < curD + 1, ∀ T ∈ slotTrees, T.deg ≠ d := by
        intro d hd T hT
        rcases Nat.lt_succ_iff_lt_or_eq.mp hd with hlt | rfl
        · exact hcleared d hlt T hT
        · exact hnone T hT
      obtain ⟨b, finalRoots, t_tl, he_tl, ht_tl, hb_b, hbr_b, hmod_tl, hregs_tl,
        hperm_b, hnd_b, hk_b, hp_b, hch_b, hd_b, hmk_b, hin_b, hnm_b, hsz_b,
        hcons_b, hnr_b, hval_b, hrl_b⟩ :=
        ih a3 (curD + 1) slotTrees accRoots z (by omega) hb3 hbr3
          (by simp only [a3, Data.set_regs, Function.update_self])
          (by simp only [a3, a2, a1, Data.set_regs,
                Function.update_of_ne (by decide : maxDegReg ≠ curDReg),
                Function.update_of_ne (by decide : maxDegReg ≠ s0),
                Function.update_of_ne (by decide : maxDegReg ≠ s3), hmaxD])
          (hst3 ▸ hs) hcleared3 hnd (hst3 ▸ hacc) (hst3 ▸ hnr) (hst3 ▸ hrl)
      rw [hst3] at hk_b hp_b hch_b hd_b hmk_b hin_b hnm_b hsz_b
      refine ⟨b, finalRoots, 6 + t_tl + 2, ExecWithin.loop_iter hc_loop he_body he_tl,
        by omega, hb_b, hbr_b, hmod_tl, ?_, hperm_b, hnd_b,
        ⟨hk_b, hp_b, hch_b, hd_b, hmk_b, hin_b, hnm_b, hsz_b, hcons_b, hnr_b, hval_b, hrl_b⟩⟩
      intro r hr hrm hrnr
      have ne_cd : r ≠ curDReg := fun e => by subst e; change 34 < 30 at hr; omega
      have ne_s0 : r ≠ s0 := fun e => by subst e; change 35 < 30 at hr; omega
      have ne_s3 : r ≠ s3 := fun e => by subst e; change 38 < 30 at hr; omega
      rw [hregs_tl r hr hrm hrnr]
      simp only [a3, a2, a1, Data.set_regs, Function.update_of_ne ne_cd,
        Function.update_of_ne ne_s0, Function.update_of_ne ne_s3]
    · -- Occupied slot (`T_hit = slotTrees[idx]`)
      let T_hit := slotTrees[idx]
      let u := T_hit.root
      let slotRest := slotTrees.eraseIdx idx
      have hc_br : (Cond.lt zeroP s3).Holds a1 := by
        simp only [Cond.Holds, hbr1.2.2.2.2.2.2.2.2.2.2.2.1, ha1_s3, hcons_eq]; omega
      have ho_cons := owns_cons_addr (base := base) hd_le_n
      let a2 := a1.write (base + 8 * n + curD) 0
      let a3 := a2.set iterCur u.val
      have s_st0 : ExecWithin (B := .exact) w (.op (.store s0 zeroP)) a1 a2 1 := by
        simpa only [ha1_s0, hbr1.2.2.2.2.2.2.2.2.2.2.2.1] using
          (ExecWithin.store (B := .exact) (w := w) (x := a1) (a := s0) (s := zeroP))
      have ha2_s3 : a2.regs s3 = u.val + 1 := by
        simp only [a2, Data.write_regs, ha1_s3, hcons_eq]; rfl
      have ha2_o1 : a2.regs oneP = 1 := hbr1.2.2.2.2.2.2.2.2.2.2.2.2
      have s_sub0 : ExecWithin w (.op (.exactBin .sub iterCur s3 oneP)) a2 a3 1 := by
        have := u.isLt
        simpa only [ha2_s3, ha2_o1, Nat.add_sub_cancel] using
          execWithin_exactSub (x := a2) (d := iterCur) (i := s3) (j := oneP)
            (by rw [ha2_s3, ha2_o1]; omega)
            (by rw [ha2_s3, ha2_o1]; exact hfit_stop.of_le (by simp only [space]; omega))
      have hb3 : a3.Bounded w := s_sub0.bounded (s_st0.bounded hb1)
      have hbr3 : BaseRegs n base a3 := (hbr1.write_eq _ _).set_non_base (by decide) _
      have hst3 : RawState.ofData n base a3 =
          { st with cons := Function.update st.cons curD 0 } := by
        have hc_wr := ofData_write_cons (base := base) hd_le_n a1 0
        rw [hst1] at hc_wr
        exact (ofData_set_scratch a2 (by decide : 17 ≤ iterCur.val) u.val).trans hc_wr
      have hperm_er : (T_hit.nodes ++ forestNodes slotRest).Perm (forestNodes slotTrees) :=
        forestNodes_eraseIdx_perm slotTrees idx hidx
      have hnd_next : (forestNodes slotRest ++ (z :: forestNodes (T_hit :: accRoots))).Nodup :=
        (perm_move_to_acc T_hit.nodes (forestNodes slotRest) z (forestNodes accRoots)).nodup_iff.mp
          ((hperm_er.append_right _).nodup_iff.mpr hnd)
      have hnd_add : (forestNodes (T_hit :: accRoots)).Nodup :=
        (List.nodup_cons.mp (List.nodup_append.mp hnd_next).2.1).2
      have hThit_val3 : ValidRoot (RawState.ofData n base a3) none T_hit := by
        rw [hst3]
        exact (hs.2.1 T_hit (List.getElem_mem hidx)).1.frame_nodes
          fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      have hacc_val3 : ∀ T ∈ accRoots, ValidRoot (RawState.ofData n base a3) none T := by
        intro T hT
        rw [hst3]
        exact (hacc T hT).frame_nodes fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      have hrl3 : (accRoots = [] ∧ (RawState.ofData n base a3).minRoot = 0) ∨
          ∃ (m : Fin n) (rtail : List (Fin n)),
            (RawState.ofData n base a3).minRoot = m.val + 1 ∧
            IsCircList (RawState.ofData n base a3).left (RawState.ofData n base a3).right
              (m :: rtail) ∧
            (m :: rtail).Perm (accRoots.map FHTree.root) ∧
            ∀ T ∈ accRoots, IndexedMinPQ.PrioLE
              (m, (RawState.ofData n base a3).key m)
              (T.root, (RawState.ofData n base a3).key T.root) := by
        rw [hst3]; exact hrl
      have ha3_ic : a3.regs iterCur = u.val := by
        simp only [a3, Data.set_regs, Function.update_self]
      obtain ⟨a4, he_add, hbr4, hmod_add,
        hk4, hp4, hch4, hd4, hmk4, hin4, hcons4, hnm4, hsz4, hnr4, hval4, m4, rtail4, hrl4⟩ :=
        addRootAndUpdateMin_exec hb3 hbr3
          ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
          ha3_ic rfl hnd_add hThit_val3 hacc_val3 (by rw [hst3]; exact hnr) hrl3
      have hlr4 := addRootIterCur_lr_frame hb3 hbr3 ha3_ic (T_u := T_hit) (ts := accRoots) rfl
        hnd_add hrl3 he_add
      have hb4 : a4.Bounded w := he_add.bounded hb3
      let a5 := a4.set curDReg (curD + 1)
      have ha4_cd : a4.regs curDReg = curD := by
        rw [he_add.regs_eq (addRootAndUpdateMin_preserves (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide))]
        simp only [a3, a2, a1, Data.set_regs, Data.write_regs,
          Function.update_of_ne (by decide : curDReg ≠ iterCur),
          Function.update_of_ne (by decide : curDReg ≠ s3),
          Function.update_of_ne (by decide : curDReg ≠ s0), hcurD]
      have ha4_o1 : a4.regs oneP = 1 := hbr4.2.2.2.2.2.2.2.2.2.2.2.2
      have he_inc : ExecWithin w (.op (.exactBin .add curDReg curDReg oneP)) a4 a5 1 := by
        simpa only [ha4_cd, ha4_o1] using
          execWithin_exactAdd (x := a4) (d := curDReg) (i := curDReg) (j := oneP)
            (by rw [ha4_cd, ha4_o1]; exact hfit_stop.of_le (by simp only [space]; omega))
      have he_br : ExecWithin w
          (.branch (.lt zeroP s3)
            (.seq (.op (.store s0 zeroP)) <|
             .seq (.op (.exactBin .sub iterCur s3 oneP)) (addRootAndUpdateMin iterCur))
            (.op (.copy s0 zeroP))) a1 a4 31 :=
        (ExecWithin.branch_pos hc_br (s_st0.seq (s_sub0.seq he_add))).mono (by omega)
      have he_body : ExecWithin w gatherSlotBody a a5 34 := by
        unfold gatherSlotBody
        exact (s_add0.seq <| s_ld0.seq <| he_br.seq he_inc).mono (by omega)
      have hb5 : a5.Bounded w := he_inc.bounded hb4
      have hbr5 : BaseRegs n base a5 := hbr4.set_non_base (by decide) _
      have hst5 : RawState.ofData n base a5 = RawState.ofData n base a4 :=
        ofData_set_scratch a4 (by decide : 17 ≤ curDReg.val) (curD + 1)
      have hmod5 : Modifies (Block.mk base (space n)).footprint a.mem a5.mem :=
        modifies_block_trans (Modifies.write_of_owns ho_cons 0) hmod_add
      have hs5 : SlotInv n (RawState.ofData n base a5) slotRest maxDeg := by
        rw [hst5]
        refine hs.step_collision hidx hslot_deg hd_le_n hno_other
          (by rw [hcons4, hst3]) fun R hR => ?_
        obtain ⟨j, hj, _, hR_eq⟩ := List.mem_eraseIdx_iff_getElem.mp hR
        have hR_st : ValidRoot st none R := hR_eq ▸ (hs.2.1 _ (List.getElem_mem hj)).1
        refine hR_st.frame_tree
          (fun w' _ => ⟨by rw [hin4, hst3], by rw [hmk4, hst3], by rw [hd4, hst3],
            by rw [hch4, hst3], by rw [hk4, hst3], by rw [hp4, hst3]⟩)
          (fun w' hw' => ?_)
        have hw_rest : w' ∈ forestNodes slotRest :=
          mem_forestNodes_iff.mpr ⟨R, hR, R.nodes_eq ▸ List.mem_cons_of_mem R.root hw'⟩
        have hw_not_roots : w' ∉ (T_hit :: accRoots).map FHTree.root := by
          intro hm_in
          obtain ⟨Q, hQ, rfl⟩ := List.mem_map.mp hm_in
          have hQ_fn : Q.root ∈ z :: forestNodes (T_hit :: accRoots) :=
            List.mem_cons_of_mem z (mem_forestNodes_iff.mpr ⟨Q, hQ, Q.root_mem_nodes⟩)
          exact (List.nodup_append.mp hnd_next).2.2 Q.root hw_rest Q.root hQ_fn rfl
        have hlr_w := hlr4 w' hw_not_roots
        rw [hst3] at hlr_w
        exact hlr_w
      have hcleared5 : ∀ d < curD + 1, ∀ R ∈ slotRest, R.deg ≠ d := by
        intro d hd R hR
        rcases Nat.lt_succ_iff_lt_or_eq.mp hd with hlt | rfl
        · obtain ⟨j, hj, _, rfl⟩ := List.mem_eraseIdx_iff_getElem.mp hR
          exact hcleared d hlt _ (List.getElem_mem hj)
        · exact hno_other R hR
      obtain ⟨b, finalRoots, t_tl, he_tl, ht_tl, hb_b, hbr_b, hmod_tl, hregs_tl,
        hperm_b, hnd_b, hk_b, hp_b, hch_b, hd_b, hmk_b, hin_b, hnm_b, hsz_b,
        hcons_b, hnr_b, hval_b, hrl_b⟩ :=
        ih a5 (curD + 1) slotRest (T_hit :: accRoots) z (by omega) hb5 hbr5
          (by simp only [a5, Data.set_regs, Function.update_self])
          (by
            simp only [a5, Data.set_regs, Function.update_of_ne (by decide : maxDegReg ≠ curDReg)]
            rw [he_add.regs_eq (addRootAndUpdateMin_preserves (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide))]
            simp only [a3, a2, a1, Data.set_regs, Data.write_regs,
              Function.update_of_ne (by decide : maxDegReg ≠ iterCur),
              Function.update_of_ne (by decide : maxDegReg ≠ s3),
              Function.update_of_ne (by decide : maxDegReg ≠ s0), hmaxD])
          hs5 hcleared5 hnd_next (by rw [hst5]; exact hval4) (by rw [hst5]; exact hnr4)
          (by rw [hst5]; exact Or.inr ⟨m4, rtail4, hrl4⟩)
      have he_all : ExecWithin w gatherSlotsLoop a b (34 + t_tl + 2) :=
        ExecWithin.loop_iter hc_loop he_body he_tl
      have hperm_final :
          (forestNodes finalRoots).Perm (forestNodes slotTrees ++ forestNodes accRoots) :=
        hperm_b.trans <| (perm_swap_front (forestNodes slotRest) T_hit.nodes
          (forestNodes accRoots)).trans <| by
          rw [← List.append_assoc]
          exact hperm_er.append_right _
      rw [hst5] at hk_b hp_b hch_b hd_b hmk_b hin_b hnm_b hsz_b
      rw [hst3] at hk4 hp4 hch4 hd4 hmk4 hin4 hnm4 hsz4
      refine ⟨b, finalRoots, 34 + t_tl + 2, he_all,
        by simp only [List.length_cons, unitCredit] at ht_tl ⊢; omega,
        hb_b, hbr_b, modifies_block_trans hmod5 hmod_tl, ?_, hperm_final, hnd_b,
        ⟨hk_b.trans hk4, hp_b.trans hp4, hch_b.trans hch4, hd_b.trans hd4,
          hmk_b.trans hmk4, hin_b.trans hin4, hnm_b.trans hnm4, hsz_b.trans hsz4,
          hcons_b, hnr_b, hval_b, hrl_b⟩⟩
      intro r hr hrm hrnr
      have ne_cd : r ≠ curDReg := fun e => by subst e; change 34 < 30 at hr; omega
      have ne_ic : r ≠ iterCur := fun e => by subst e; change 31 < 30 at hr; omega
      have ne_s0 : r ≠ s0 := fun e => by subst e; change 35 < 30 at hr; omega
      have ne_s1 : r ≠ s1 := fun e => by subst e; change 36 < 30 at hr; omega
      have ne_s2 : r ≠ s2 := fun e => by subst e; change 37 < 30 at hr; omega
      have ne_s3 : r ≠ s3 := fun e => by subst e; change 38 < 30 at hr; omega
      have ne_s4 : r ≠ s4 := fun e => by subst e; change 39 < 30 at hr; omega
      have ne_s5 : r ≠ s5 := fun e => by subst e; change 40 < 30 at hr; omega
      rw [hregs_tl r hr hrm hrnr]
      simp only [a5, Data.set_regs, Function.update_of_ne ne_cd]
      rw [he_add.regs_eq (addRootAndUpdateMin_preserves ne_s0 ne_s1 ne_s2 ne_s3 ne_s4 ne_s5
        hrm hrnr)]
      simp only [a3, a2, a1, Data.set_regs, Data.write_regs,
        Function.update_of_ne ne_ic, Function.update_of_ne ne_s3, Function.update_of_ne ne_s0]

/-! ## `extractMinCode` correctness and `O(log n)` amortized bound -/

private theorem execWithin_seq₂ {B : Basis} {r w t₁ t₂ : ℕ} {a b c : Code B r}
    {x y z : Data r} (h₁ : ExecWithin w (a.seq b) x y t₁) (h₂ : ExecWithin w c y z t₂) :
    ExecWithin w (a.seq (b.seq c)) x z (t₁ + t₂) := by
  rcases h₁ with ⟨_, hm₁, ea⟩
  cases ea with | seq ha hb =>
  rcases h₂ with ⟨_, hm₂, hc⟩
  exact ⟨_, by omega, ha.seq (hb.seq hc)⟩

private theorem execWithin_seq₃ {B : Basis} {r w t₁ t₂ : ℕ} {a b c d : Code B r}
    {x y z : Data r} (h₁ : ExecWithin w (a.seq (b.seq c)) x y t₁) (h₂ : ExecWithin w d y z t₂) :
    ExecWithin w (a.seq (b.seq (c.seq d))) x z (t₁ + t₂) := by
  rcases h₁ with ⟨_, hm₁, ea⟩
  cases ea with | seq ha ebc =>
  cases ebc with | seq hb hc =>
  rcases h₂ with ⟨_, hm₂, hd⟩
  exact ⟨_, by omega, ha.seq (hb.seq (hc.seq hd))⟩

/-- `extractMinCode` implements `.extractMin` on `FibInv` within `410 * (Nat.log 2 n + 1)`
amortized instructions (`t + potential y ≤ 410 * (Nat.log 2 n + 1) + potential x`). -/
theorem extractMinCode_exec {n K_max w base : ℕ} {s : IndexedMinPQ.State n} {x : Data rFib}
    (hinv : FibInv n K_max w base s x) :
    ∃ y t, ExecWithin w extractMinCode x y t ∧
      code.decode (n := n) (K_max := K_max) .extractMin y.regs =
        some ((IndexedMinPQ.spec n K_max).step s .extractMin).2 ∧
      FibInv n K_max w base ((IndexedMinPQ.spec n K_max).step s .extractMin).1 y ∧
      Modifies (Block.mk base (space n)).footprint x.mem y.mem ∧
      t + potential y ≤ 410 * (Nat.log 2 n + 1) + potential x := by
  obtain ⟨hb, hbr, hraw⟩ := hinv
  set st := RawState.ofData n base x with hst_def
  have hfit_stop := hbr.fits_stop hb
  have hz0 : x.regs zeroP = 0 := hbr.2.2.2.2.2.2.2.2.2.2.2.1
  have ho1 : x.regs oneP = 1 := hbr.2.2.2.2.2.2.2.2.2.2.2.2
  by_cases hm0 : st.minRoot = 0
  · -- Empty heap (`minRoot = 0`)
    have hc : (Cond.eq minRootReg zeroP).Holds x := by
      simp only [Cond.Holds, hz0]; exact hm0
    let y := x.set outFlag 0
    have he : ExecWithin w extractMinCode x y 2 := by
      unfold extractMinCode
      exact ExecWithin.branch_pos hc (by
        simpa only [hz0] using
          (ExecWithin.copy (B := .exact) (w := w) (x := x) (d := outFlag) (s := zeroP)))
    obtain ⟨_, hfind⟩ := hraw.findMin_eq_none hm0
    have hpot : potential y = potential x :=
      potential_supported fun i hi => by
        have hne : i ≠ outFlag := fun e => by subst e; cases hi
        simp only [y, Data.set_regs, Function.update_of_ne hne]
    refine ⟨y, 2, he, ?_, ?_, Modifies.refl _ _, by omega⟩
    · simp only [PQCode.decode, code, IndexedMinPQ.spec, hfind, y, Data.set_regs,
        Function.update_self, ↓reduceIte]
    · simp only [IndexedMinPQ.spec, hfind]
      exact ⟨he.bounded hb, hbr.set_non_base (by decide) 0,
        (ofData_set_scratch x (by decide : 17 ≤ outFlag.val) 0).symm ▸ hraw⟩
  · -- Non-empty heap (`st.minRoot = z.val + 1`)
    have hc_top : ¬(Cond.eq minRootReg zeroP).Holds x := by
      simp only [Cond.Holds, hz0]; exact hm0
    have hraw_copy := hraw
    obtain ⟨ts, hroots, hnd, hdom, hin_iff, hkeys, hsz, hnr, hnm, hcons, hrl⟩ := hraw
    rcases hrl with ⟨_, h0⟩ | ⟨z, rtail, hmin_z, hcirc_roots, hperm_roots, _⟩
    · exact absurd h0 hm0
    have hz_lt := z.isLt
    have hn_pos : 1 ≤ n := by omega
    obtain ⟨hfind, hsz_some, _⟩ := hraw_copy.findMin_eq_some hmin_z
    have hz_dom : z ∈ IndexedMinPQ.dom s := IndexedMinPQ.mem_dom_iff.mpr ⟨st.key z, hsz_some⟩
    have hsz_pos : 1 ≤ st.sz := by
      have : 0 < (IndexedMinPQ.dom s).card := Finset.card_pos.mpr ⟨z, hz_dom⟩
      omega
    obtain ⟨idx_z, hidx_z, hTz_root, hperm_rtail, hperm_ts⟩ :=
      extract_tree_by_root hnd hperm_roots
    let T_z := ts[idx_z]
    let r_trees := ts.eraseIdx idx_z
    have hnr_split : r_trees.length + 1 = ts.length := length_eraseIdx_add_one ts idx_z hidx_z
    have hrtail_len : rtail.length = r_trees.length := by
      simpa only [List.length_map] using hperm_rtail.length_eq
    have hTz_val : ValidRoot st none T_z := hroots T_z (List.getElem_mem hidx_z)
    have hts_len_le_n : (forestNodes ts).length ≤ n := by simpa using hnd.length_le_card
    have hTz_size_le_n : T_z.size ≤ n := by
      have h1 := hperm_ts.length_eq
      simp only [List.length_append] at h1
      change (ts[idx_z]).nodes.length ≤ n
      omega
    have hTz_deg_log : T_z.deg ≤ 2 * Nat.log 2 n + 1 :=
      (hTz_val.1.deg_bounds hTz_size_le_n).1
    rcases hTz_eq : T_z with ⟨z', c_trees⟩
    have hzz' : z' = z := by
      have hr : T_z.root = z := hTz_root
      simpa only [hTz_eq, FHTree.root_node] using hr
    subst z'
    have hTz_val' : ValidRoot st none (FHTree.node z c_trees) := hTz_eq ▸ hTz_val
    have hmk_z0 : st.mark z = 0 := hTz_val'.2.2
    simp only [hTz_eq, FHTree.deg_node] at hTz_deg_log
    cases hTz_val'.1 with
    | mk _ _ hdeg_z hchild_z _ _ _ hsub_z =>
      -- Node disjointness across `T_z` and `r_trees`
      have hnd_split : ((z :: forestNodes c_trees) ++ forestNodes r_trees).Nodup := by
        have hp0 : (T_z.nodes ++ forestNodes r_trees).Perm (forestNodes ts) := hperm_ts
        have hp : ((z :: forestNodes c_trees) ++ forestNodes r_trees).Perm (forestNodes ts) := by
          simpa only [hTz_eq, FHTree.nodes] using hp0
        exact hp.nodup_iff.mpr hnd
      have hz_not_cr : z ∉ forestNodes c_trees ++ forestNodes r_trees := by
        rw [List.cons_append] at hnd_split
        exact (List.nodup_cons.mp hnd_split).1
      -- Preamble (`x → x_pre`, 13 instructions)
      have hbb : x.regs baseReg = base := hbr.2.2.1
      have hcb : x.regs childBase = base + 2 * n := hbr.2.2.2.2.1
      have hrb : x.regs rightBase = base + 4 * n := hbr.2.2.2.2.2.2.1
      have hdb : x.regs degBase = base + 5 * n := hbr.2.2.2.2.2.2.2.1
      have hinb : x.regs inBase = base + 7 * n := hbr.2.2.2.2.2.2.2.2.2.1
      have ho_in_z := owns_arr_addr (base := base) (k := 7) (by decide) hz_lt
      let p1 := x.set zReg z.val
      let p2 := (p1.set outFlag 1).set outV z.val
      let p3 := (p2.set s0 (base + z.val)).set outK (st.key z)
      let p4 := ((p3.set s0 (base + 7 * n + z.val)).write (base + 7 * n + z.val) 0).set szReg
        (st.sz - 1)
      let p5 := ((p4.set s0 (base + 4 * n + z.val)).set pReg (st.right z)).set maxDegReg 0
      let x_pre := (p5.set s0 (base + 5 * n + z.val)).set remReg (st.deg z)
      have ep1 : ExecWithin w (.op (.exactBin .sub zReg minRootReg oneP)) x p1 1 := by
        have hm_x : x.regs minRootReg = z.val + 1 := hmin_z
        simpa only [hm_x, ho1, Nat.add_sub_cancel] using
          execWithin_exactSub (x := x) (d := zReg) (i := minRootReg) (j := oneP)
            (by rw [hm_x, ho1]; omega)
            (by rw [hm_x, ho1]; exact hfit_stop.of_le (by simp only [space]; omega))
      have ep2 : ExecWithin (B := .exact) w
          (.seq (.op (.copy outFlag oneP)) (.op (.copy outV zReg))) p1 p2 2 := by
        have s_of : ExecWithin (B := .exact) w (.op (.copy outFlag oneP)) p1 (p1.set outFlag 1) 1 :=
          by simpa only [p1, Data.set_regs, Function.update_of_ne (by decide : oneP ≠ zReg), ho1]
               using (ExecWithin.copy (B := .exact) (w := w) (x := p1) (d := outFlag) (s := oneP))
        have s_ov : ExecWithin (B := .exact) w (.op (.copy outV zReg)) (p1.set outFlag 1) p2 1 := by
          simpa only [p2, p1, Data.set_regs, Function.update_of_ne (by decide : zReg ≠ outFlag),
            Function.update_self] using
            (ExecWithin.copy (B := .exact) (w := w) (x := p1.set outFlag 1) (d := outV) (s := zReg))
        exact (s_of.seq s_ov).mono (by omega)
      have ep3 : ExecWithin w
          (.seq (.op (.exactBin .add s0 baseReg zReg)) (.op (.load outK s0))) p2 p3 2 := by
        have hb_p2 : p2.regs baseReg = base := hbb
        have hz_p2 : p2.regs zReg = z.val := by
          simp only [p2, p1, Data.set_regs, Function.update_of_ne (by decide : zReg ≠ outV),
            Function.update_of_ne (by decide : zReg ≠ outFlag), Function.update_self]
        have s_a : ExecWithin w (.op (.exactBin .add s0 baseReg zReg)) p2
            (p2.set s0 (base + z.val)) 1 := by
          simpa only [hb_p2, hz_p2] using
            execWithin_exactAdd (x := p2) (d := s0) (i := baseReg) (j := zReg)
              (by rw [hb_p2, hz_p2]; exact hfit_stop.of_le (by simp only [space]; omega))
        have s_l : ExecWithin (B := .exact) w (.op (.load outK s0))
            (p2.set s0 (base + z.val)) p3 1 := by
          have hkz : x.mem (base + z.val) = st.key z := rfl
          simpa only [p3, p2, p1, Data.set_mem, Data.set_regs, Function.update_self, hkz] using
            (ExecWithin.load (B := .exact) (w := w) (x := p2.set s0 (base + z.val))
              (d := outK) (a := s0))
        exact (s_a.seq s_l).mono (by omega)
      have ep4 : ExecWithin w
          (.seq (.op (.exactBin .add s0 inBase zReg)) <|
           .seq (.op (.store s0 zeroP))
                (.op (.exactBin .sub szReg szReg oneP))) p3 p4 3 := by
        have hin_p3 : p3.regs inBase = base + 7 * n := hinb
        have hz_p3 : p3.regs zReg = z.val := by
          simp only [p3, p2, p1, Data.set_regs, Function.update_of_ne (by decide : zReg ≠ outK),
            Function.update_of_ne (by decide : zReg ≠ s0),
            Function.update_of_ne (by decide : zReg ≠ outV),
            Function.update_of_ne (by decide : zReg ≠ outFlag), Function.update_self]
        have s_a : ExecWithin w (.op (.exactBin .add s0 inBase zReg)) p3
            (p3.set s0 (base + 7 * n + z.val)) 1 := by
          simpa only [hin_p3, hz_p3] using
            execWithin_exactAdd (x := p3) (d := s0) (i := inBase) (j := zReg)
              (by rw [hin_p3, hz_p3]; exact hfit_stop.of_le (by simp only [space]; omega))
        have s_st : ExecWithin (B := .exact) w (.op (.store s0 zeroP))
            (p3.set s0 (base + 7 * n + z.val))
            ((p3.set s0 (base + 7 * n + z.val)).write (base + 7 * n + z.val) 0) 1 := by
          have hz0_p3 : (p3.set s0 (base + 7 * n + z.val)).regs zeroP = 0 := hz0
          simpa only [Data.set_regs, Function.update_self, hz0_p3] using
            (ExecWithin.store (B := .exact) (w := w) (x := p3.set s0 (base + 7 * n + z.val))
              (a := s0) (s := zeroP))
        have hsz_w : ((p3.set s0 (base + 7 * n + z.val)).write (base + 7 * n + z.val) 0).regs
            szReg = st.sz := rfl
        have ho1_w : ((p3.set s0 (base + 7 * n + z.val)).write (base + 7 * n + z.val) 0).regs
            oneP = 1 := ho1
        have hsz_le_n : st.sz ≤ n := hraw_copy.bounds.1
        have s_sub : ExecWithin w (.op (.exactBin .sub szReg szReg oneP))
            ((p3.set s0 (base + 7 * n + z.val)).write (base + 7 * n + z.val) 0) p4 1 := by
          simpa only [p4, hsz_w, ho1_w] using
            execWithin_exactSub
              (x := (p3.set s0 (base + 7 * n + z.val)).write (base + 7 * n + z.val) 0)
              (d := szReg) (i := szReg) (j := oneP)
              (by rw [hsz_w, ho1_w]; omega)
              (by rw [hsz_w, ho1_w]; exact hfit_stop.of_le (by simp only [space]; omega))
        exact (s_a.seq (s_st.seq s_sub)).mono (by omega)
      have ep5 : ExecWithin w
          (.seq (.op (.exactBin .add s0 rightBase zReg)) <|
           .seq (.op (.load pReg s0))
                (.op (.copy maxDegReg zeroP))) p4 p5 3 := by
        have hr_p4 : p4.regs rightBase = base + 4 * n := hrb
        have hz_p4 : p4.regs zReg = z.val := by
          simp only [p4, p3, p2, p1, Data.set_regs, Data.write_regs,
            Function.update_of_ne (by decide : zReg ≠ szReg),
            Function.update_of_ne (by decide : zReg ≠ outK),
            Function.update_of_ne (by decide : zReg ≠ s0),
            Function.update_of_ne (by decide : zReg ≠ outV),
            Function.update_of_ne (by decide : zReg ≠ outFlag), Function.update_self]
        have s_a : ExecWithin w (.op (.exactBin .add s0 rightBase zReg)) p4
            (p4.set s0 (base + 4 * n + z.val)) 1 := by
          simpa only [hr_p4, hz_p4] using
            execWithin_exactAdd (x := p4) (d := s0) (i := rightBase) (j := zReg)
              (by rw [hr_p4, hz_p4]; exact hfit_stop.of_le (by simp only [space]; omega))
        have s_l : ExecWithin (B := .exact) w (.op (.load pReg s0))
            (p4.set s0 (base + 4 * n + z.val))
            ((p4.set s0 (base + 4 * n + z.val)).set pReg (st.right z)) 1 := by
          have hrz : (p4.set s0 (base + 4 * n + z.val)).mem (base + 4 * n + z.val) =
              st.right z := by
            simp only [p4, p3, p2, p1, Data.set_mem, Data.write_mem,
              Function.update_of_ne (by omega : base + 4 * n + z.val ≠ base + 7 * n + z.val)]
            rfl
          simpa only [Data.set_regs, Function.update_self, hrz] using
            (ExecWithin.load (B := .exact) (w := w) (x := p4.set s0 (base + 4 * n + z.val))
              (d := pReg) (a := s0))
        have s_c : ExecWithin (B := .exact) w (.op (.copy maxDegReg zeroP))
            ((p4.set s0 (base + 4 * n + z.val)).set pReg (st.right z)) p5 1 := by
          have hz0_p4 : ((p4.set s0 (base + 4 * n + z.val)).set pReg (st.right z)).regs zeroP =
              0 := hz0
          simpa only [p5, hz0_p4] using
            (ExecWithin.copy (B := .exact) (w := w)
              (x := (p4.set s0 (base + 4 * n + z.val)).set pReg (st.right z))
              (d := maxDegReg) (s := zeroP))
        exact (s_a.seq (s_l.seq s_c)).mono (by omega)
      have ep6 : ExecWithin w
          (.seq (.op (.exactBin .add s0 degBase zReg)) (.op (.load remReg s0))) p5 x_pre 2 := by
        have hd_p5 : p5.regs degBase = base + 5 * n := hdb
        have hz_p5 : p5.regs zReg = z.val := by
          simp only [p5, p4, p3, p2, p1, Data.set_regs, Data.write_regs,
            Function.update_of_ne (by decide : zReg ≠ maxDegReg),
            Function.update_of_ne (by decide : zReg ≠ pReg),
            Function.update_of_ne (by decide : zReg ≠ szReg),
            Function.update_of_ne (by decide : zReg ≠ outK),
            Function.update_of_ne (by decide : zReg ≠ s0),
            Function.update_of_ne (by decide : zReg ≠ outV),
            Function.update_of_ne (by decide : zReg ≠ outFlag), Function.update_self]
        have s_a : ExecWithin w (.op (.exactBin .add s0 degBase zReg)) p5
            (p5.set s0 (base + 5 * n + z.val)) 1 := by
          simpa only [hd_p5, hz_p5] using
            execWithin_exactAdd (x := p5) (d := s0) (i := degBase) (j := zReg)
              (by rw [hd_p5, hz_p5]; exact hfit_stop.of_le (by simp only [space]; omega))
        have s_l : ExecWithin (B := .exact) w (.op (.load remReg s0))
            (p5.set s0 (base + 5 * n + z.val)) x_pre 1 := by
          have hdz : (p5.set s0 (base + 5 * n + z.val)).mem (base + 5 * n + z.val) =
              st.deg z := by
            simp only [p5, p4, p3, p2, p1, Data.set_mem, Data.write_mem,
              Function.update_of_ne (by omega : base + 5 * n + z.val ≠ base + 7 * n + z.val)]
            rfl
          simpa only [x_pre, Data.set_regs, Function.update_self, hdz] using
            (ExecWithin.load (B := .exact) (w := w) (x := p5.set s0 (base + 5 * n + z.val))
              (d := remReg) (a := s0))
        exact (s_a.seq s_l).mono (by omega)
      have hb_pre : x_pre.Bounded w :=
        ep6.bounded (ep5.bounded (ep4.bounded (ep3.bounded (ep2.bounded (ep1.bounded hb)))))
      have hbr_pre : BaseRegs n base x_pre :=
        (((((((((((hbr.set_non_base (by decide) _).set_non_base (by decide) _).set_non_base
          (by decide) _).set_non_base (by decide) _).set_non_base (by decide) _).set_non_base
          (by decide) _).write_eq _ _).set_non_base (by decide) _).set_non_base
          (by decide) _).set_non_base (by decide) _).set_non_base (by decide) _).set_non_base
          (by decide) _ |>.set_non_base (by decide) _
      have hmod_pre : Modifies (Block.mk base (space n)).footprint x.mem x_pre.mem :=
        Modifies.write_of_owns ho_in_z 0
      have hst_pre : RawState.ofData n base x_pre =
          { st with inHeap := Function.update st.inHeap z 0, sz := st.sz - 1 } := by
        have hin_wr : RawState.ofData n base
            ((p3.set s0 (base + 7 * n + z.val)).write (base + 7 * n + z.val) 0) =
            { st with inHeap := Function.update st.inHeap z 0 } := by
          have h := ofData_write_inHeap (base := base) (p3.set s0 (base + 7 * n + z.val)) z 0
          have hp3_eq : RawState.ofData n base (p3.set s0 (base + 7 * n + z.val)) = st := by
            simp only [p3, p2, p1, ofData_set_scratch _ (by decide : 17 ≤ s0.val),
              ofData_set_scratch _ (by decide : 17 ≤ outK.val),
              ofData_set_scratch _ (by decide : 17 ≤ outV.val),
              ofData_set_scratch _ (by decide : 17 ≤ outFlag.val),
              ofData_set_scratch _ (by decide : 17 ≤ zReg.val), hst_def]
          rw [hp3_eq] at h
          exact h
        simp only [x_pre, p5, p4, ofData_set_scratch _ (by decide : 17 ≤ remReg.val),
          ofData_set_scratch _ (by decide : 17 ≤ s0.val),
          ofData_set_scratch _ (by decide : 17 ≤ maxDegReg.val),
          ofData_set_scratch _ (by decide : 17 ≤ pReg.val),
          ofData_set_sz, hin_wr]
      have hnm_pre : (RawState.ofData n base x_pre).numMarked =
          markedCount (RawState.ofData n base x_pre) := by
        have hnum : (RawState.ofData n base x_pre).numMarked = st.numMarked := by rw [hst_pre]
        rw [hnum, hnm]
        refine (markedCount_congr fun u => ?_).symm
        rw [hst_pre]
        by_cases huz : u = z
        · subst huz
          simp only [Function.update_self, hmk_z0, ne_eq, not_true_eq_false, and_false]
        · simp only [Function.update_of_ne huz]
      have hnd_crz : (forestNodes c_trees ++ ([] ++ (forestNodes r_trees ++ [z]))).Nodup := by
        simp only [List.nil_append]
        have hp : ([z] ++ (forestNodes c_trees ++ forestNodes r_trees)).Perm
            ((forestNodes c_trees ++ forestNodes r_trees) ++ [z]) := List.perm_append_comm
        simp only [List.singleton_append, List.append_assoc] at hp
        rw [List.cons_append] at hnd_split
        exact hp.nodup_iff.mp hnd_split
      -- Phase A1 (`x_pre → x_A1`)
      have hA1 : ∃ x_A1 slotTrees_1 maxDeg_1 t_A1,
          ExecWithin w
            (.branch (.lt zeroP remReg)
              (.seq (.op (.exactBin .add s0 childBase zReg)) <|
               .seq (.op (.load s1 s0)) <|
               .seq (.op (.exactBin .sub iterCur s1 oneP)) childScatterLoop)
              (.op (.copy s0 zeroP))) x_pre x_A1 t_A1 ∧
          t_A1 + slotCredit * slotTrees_1.length ≤ 7 + 76 * c_trees.length ∧
          x_A1.Bounded w ∧ BaseRegs n base x_A1 ∧
          Modifies (Block.mk base (space n)).footprint x_pre.mem x_A1.mem ∧
          (∀ r : Fin rFib, r.val < 30 → r ≠ numMarkedReg → x_A1.regs r = x_pre.regs r) ∧
          x_A1.regs maxDegReg = maxDeg_1 ∧
          (forestNodes slotTrees_1).Perm (forestNodes c_trees) ∧
          (forestNodes slotTrees_1 ++ (forestNodes r_trees ++ [z])).Nodup ∧
          SlotInv n (RawState.ofData n base x_A1) slotTrees_1 maxDeg_1 ∧
          (let st' := RawState.ofData n base x_A1
           st'.key = st.key ∧ st'.inHeap = Function.update st.inHeap z 0 ∧
           st'.minRoot = st.minRoot ∧ st'.numRoots = st.numRoots ∧ st'.sz = st.sz - 1 ∧
           st'.numMarked = markedCount st' ∧ st'.numMarked ≤ st.numMarked ∧
           ∀ v ∈ forestNodes r_trees ++ [z],
             st'.par v = st.par v ∧ st'.child v = st.child v ∧
             st'.left v = st.left v ∧ st'.right v = st.right v ∧
             st'.deg v = st.deg v ∧ st'.mark v = st.mark v) := by
        have hz_pre0 : x_pre.regs zeroP = 0 := hbr_pre.2.2.2.2.2.2.2.2.2.2.2.1
        have hrem_pre : x_pre.regs remReg = st.deg z := by
          simp only [x_pre, Data.set_regs, Function.update_self]
        rcases hchild_z with ⟨rfl, _⟩ | ⟨h_c, c_tail, hcz, hcirc_c, hperm_c⟩
        · have hc_rem : ¬(Cond.lt zeroP remReg).Holds x_pre := by
            simp only [Cond.Holds, hz_pre0, hrem_pre, hdeg_z, List.length_nil, Nat.lt_irrefl,
              not_false_eq_true]
          let x_A1 := x_pre.set s0 0
          have he_br : ExecWithin (B := .exact) w
              (.branch (.lt zeroP remReg)
                (.seq (.op (.exactBin .add s0 childBase zReg)) <|
                 .seq (.op (.load s1 s0)) <|
                 .seq (.op (.exactBin .sub iterCur s1 oneP)) childScatterLoop)
                (.op (.copy s0 zeroP))) x_pre x_A1 3 :=
            ExecWithin.branch_neg hc_rem (by
              simpa only [hz_pre0] using
                (ExecWithin.copy (B := .exact) (w := w) (x := x_pre) (d := s0) (s := zeroP)))
          have hst_A1 : RawState.ofData n base x_A1 = RawState.ofData n base x_pre :=
            ofData_set_scratch x_pre (by decide : 17 ≤ s0.val) 0
          refine ⟨x_A1, [], 0, 3, he_br, by simp only [List.length_nil, Nat.mul_zero]; omega,
            he_br.bounded hb_pre,
            hbr_pre.set_non_base (by decide) 0, Modifies.refl _ _,
            fun r hr _ => by
              have ne0 : r ≠ s0 := fun e => by subst e; change 35 < 30 at hr; omega
              simp only [x_A1, Data.set_regs, Function.update_of_ne ne0],
            by simp only [x_A1, x_pre, p5, Data.set_regs,
                 Function.update_of_ne (by decide : maxDegReg ≠ s0),
                 Function.update_of_ne (by decide : maxDegReg ≠ remReg), Function.update_self],
            List.Perm.refl _,
            by simpa only [forestNodes, List.nil_append] using hnd_crz,
            SlotInv.empty (by rw [hst_A1, hst_pre]; exact hcons), ?_⟩
          dsimp only
          rw [hst_A1]
          refine ⟨by rw [hst_pre], by rw [hst_pre], by rw [hst_pre], by rw [hst_pre],
            by rw [hst_pre], hnm_pre, by rw [hst_pre],
            fun _ _ => ⟨by rw [hst_pre], by rw [hst_pre], by rw [hst_pre], by rw [hst_pre],
              by rw [hst_pre], by rw [hst_pre]⟩⟩
        · have hc_len : c_trees.length = (h_c :: c_tail).length := by
            simpa only [List.length_map] using hperm_c.symm.length_eq
          have hc_rem : (Cond.lt zeroP remReg).Holds x_pre := by
            simp only [Cond.Holds, hz_pre0, hrem_pre, hdeg_z, hc_len, List.length_cons]
            omega
          let x_c0 := ((x_pre.set s0 (base + 2 * n + z.val)).set s1 (h_c.val + 1)).set iterCur
            h_c.val
          have hz_pre : x_pre.regs zReg = z.val := by
            simp only [x_pre, p5, p4, p3, p2, p1, Data.set_regs, Data.write_regs,
              Function.update_of_ne (by decide : zReg ≠ remReg),
              Function.update_of_ne (by decide : zReg ≠ maxDegReg),
              Function.update_of_ne (by decide : zReg ≠ pReg),
              Function.update_of_ne (by decide : zReg ≠ szReg),
              Function.update_of_ne (by decide : zReg ≠ outK),
              Function.update_of_ne (by decide : zReg ≠ s0),
              Function.update_of_ne (by decide : zReg ≠ outV),
              Function.update_of_ne (by decide : zReg ≠ outFlag), Function.update_self]
          have s_ca : ExecWithin w (.op (.exactBin .add s0 childBase zReg)) x_pre
              (x_pre.set s0 (base + 2 * n + z.val)) 1 := by
            simpa only [hbr_pre.2.2.2.2.1, hz_pre] using
              execWithin_exactAdd (x := x_pre) (d := s0) (i := childBase) (j := zReg)
                (by rw [hbr_pre.2.2.2.2.1, hz_pre]
                    exact hfit_stop.of_le (by simp only [space]; omega))
          have s_cl : ExecWithin (B := .exact) w (.op (.load s1 s0))
              (x_pre.set s0 (base + 2 * n + z.val))
              ((x_pre.set s0 (base + 2 * n + z.val)).set s1 (h_c.val + 1)) 1 := by
            have hcz_mem : (x_pre.set s0 (base + 2 * n + z.val)).mem (base + 2 * n + z.val) =
                h_c.val + 1 := by
              have : (RawState.ofData n base x_pre).child z = st.child z := by rw [hst_pre]
              exact this.trans hcz
            simpa only [Data.set_regs, Function.update_self, hcz_mem] using
              (ExecWithin.load (B := .exact) (w := w) (x := x_pre.set s0 (base + 2 * n + z.val))
                (d := s1) (a := s0))
          have s_cs : ExecWithin w (.op (.exactBin .sub iterCur s1 oneP))
              ((x_pre.set s0 (base + 2 * n + z.val)).set s1 (h_c.val + 1)) x_c0 1 := by
            have := h_c.isLt
            have hs1_v : ((x_pre.set s0 (base + 2 * n + z.val)).set s1 (h_c.val + 1)).regs s1 =
                h_c.val + 1 := by simp only [Data.set_regs, Function.update_self]
            have ho1_v : ((x_pre.set s0 (base + 2 * n + z.val)).set s1 (h_c.val + 1)).regs oneP =
                1 := ho1
            simpa only [x_c0, hs1_v, ho1_v, Nat.add_sub_cancel] using
              execWithin_exactSub
                (x := (x_pre.set s0 (base + 2 * n + z.val)).set s1 (h_c.val + 1))
                (d := iterCur) (i := s1) (j := oneP)
                (by rw [hs1_v, ho1_v]; omega)
                (by rw [hs1_v, ho1_v]; exact hfit_stop.of_le (by simp only [space]; omega))
          have hb_c0 : x_c0.Bounded w := s_cs.bounded (s_cl.bounded (s_ca.bounded hb_pre))
          have hbr_c0 : BaseRegs n base x_c0 :=
            ((hbr_pre.set_non_base (by decide) _).set_non_base (by decide) _).set_non_base
              (by decide) _
          have hst_c0 : RawState.ofData n base x_c0 = RawState.ofData n base x_pre := by
            simp only [x_c0, ofData_set_scratch _ (by decide : 17 ≤ iterCur.val),
              ofData_set_scratch _ (by decide : 17 ≤ s1.val),
              ofData_set_scratch _ (by decide : 17 ≤ s0.val)]
          have hsub_c0 : ∀ c ∈ c_trees, ValidSubtree (RawState.ofData n base x_c0) none c := by
            intro c hc_mem
            rw [hst_c0, hst_pre]
            refine (hsub_z c hc_mem).frame (fun u hu => ?_)
              (fun u _ => ⟨rfl, rfl, rfl, Iff.rfl⟩)
            have huz : u ≠ z := fun e => hz_not_cr (List.mem_append_left _
              (mem_forestNodes_iff.mpr ⟨c, hc_mem, e ▸ hu⟩))
            exact ⟨Function.update_of_ne huz _ _, rfl, rfl, rfl, rfl⟩
          obtain ⟨x_A1, slotTrees_1, maxDeg_1, t_sc1, he_sc1, ht_sc1, hb_A1, hbr_A1, hmod_sc1,
            hregs_sc1, hmd_sc1, hperm_sc1, hnd_sc1, hs_sc1,
            hk_sc1, hin_sc1, hmin_sc1, hnr_sc1, hsz_sc1, hnm_sc1, hnm_le1, ho_sc1⟩ :=
            scatterChildrenLoop_exec (h_c :: c_tail) x_c0 c_trees [] (forestNodes r_trees ++ [z])
              z 0 hb_c0 hbr_c0 (List.mem_append_right _ (List.mem_cons_self : z ∈ [z])) hnd_crz
              (SlotInv.empty (by rw [hst_c0, hst_pre]; exact hcons)) hsub_c0 hperm_c
              (by rw [hst_c0, hst_pre]; exact hcirc_c.rightChain)
              (by simp only [x_c0, x_pre, Data.set_regs,
                    Function.update_of_ne (by decide : remReg ≠ iterCur),
                    Function.update_of_ne (by decide : remReg ≠ s1),
                    Function.update_of_ne (by decide : remReg ≠ s0),
                    Function.update_self, hdeg_z, hc_len])
              (by simp only [x_c0, x_pre, p5, Data.set_regs,
                    Function.update_of_ne (by decide : maxDegReg ≠ iterCur),
                    Function.update_of_ne (by decide : maxDegReg ≠ s1),
                    Function.update_of_ne (by decide : maxDegReg ≠ remReg),
                    Function.update_of_ne (by decide : maxDegReg ≠ s0), Function.update_self])
              (hst_c0 ▸ hnm_pre)
              (fun u _ hu => by
                cases hu
                simp only [x_c0, Data.set_regs, Function.update_self])
          have he_br : ExecWithin w
              (.branch (.lt zeroP remReg)
                (.seq (.op (.exactBin .add s0 childBase zReg)) <|
                 .seq (.op (.load s1 s0)) <|
                 .seq (.op (.exactBin .sub iterCur s1 oneP)) childScatterLoop)
                (.op (.copy s0 zeroP))) x_pre x_A1 (t_sc1 + 4) :=
            (ExecWithin.branch_pos hc_rem (s_ca.seq (s_cl.seq (s_cs.seq he_sc1)))).mono (by omega)
          rw [hst_c0, hst_pre] at hk_sc1 hin_sc1 hmin_sc1 hnr_sc1 hsz_sc1 hnm_le1 ho_sc1
          simp only [forestNodes, List.append_nil] at hperm_sc1
          refine ⟨x_A1, slotTrees_1, maxDeg_1, t_sc1 + 4, he_br,
            by rw [← hc_len] at ht_sc1; simp only [slotCredit, List.length_nil] at ht_sc1 ⊢; omega,
            hb_A1, hbr_A1, hmod_sc1, ?_, hmd_sc1, hperm_sc1, hnd_sc1, hs_sc1,
            ⟨hk_sc1, hin_sc1, hmin_sc1, hnr_sc1, hsz_sc1, hnm_sc1, hnm_le1, ho_sc1⟩⟩
          intro r hr hrnm
          have ne_ic : r ≠ iterCur := fun e => by subst e; change 31 < 30 at hr; omega
          have ne_s1 : r ≠ s1 := fun e => by subst e; change 36 < 30 at hr; omega
          have ne_s0 : r ≠ s0 := fun e => by subst e; change 35 < 30 at hr; omega
          rw [hregs_sc1 r hr hrnm]
          simp only [x_c0, Data.set_regs, Function.update_of_ne ne_ic,
            Function.update_of_ne ne_s1, Function.update_of_ne ne_s0]
      obtain ⟨x_A1, slotTrees_1, maxDeg_1, t_A1, he_A1, ht_A1, hb_A1, hbr_A1, hmod_A1,
        hregs_A1, hmd_A1, hperm_A1, hnd_A1, hs_A1,
        hk_A1, hin_A1, _, hnr_A1, hsz_A1, hnm_A1, hnm_le1, ho_A1⟩ := hA1
      -- Transition (`x_A1 → x_tr`, 2 ops): `remReg ← numRootsReg - oneP; iterCur ← pReg`
      let x_tr := (x_A1.set remReg rtail.length).set iterCur (st.right z)
      have hnr_xA1 : x_A1.regs numRootsReg = rtail.length + 1 := by
        change (RawState.ofData n base x_A1).numRoots = rtail.length + 1
        rw [hnr_A1, hnr, ← hnr_split, hrtail_len]
      have hpr_xA1 : x_A1.regs pReg = st.right z := by
        rw [hregs_A1 pReg (by decide) (by decide)]
        simp only [x_pre, p5, Data.set_regs, Function.update_of_ne (by decide : pReg ≠ remReg),
          Function.update_of_ne (by decide : pReg ≠ s0),
          Function.update_of_ne (by decide : pReg ≠ maxDegReg), Function.update_self]
      have etr1 : ExecWithin w (.op (.exactBin .sub remReg numRootsReg oneP)) x_A1
          (x_A1.set remReg rtail.length) 1 := by
        have hnr_le_n : st.numRoots ≤ n := hraw_copy.bounds.2.1
        have hr_le : rtail.length + 1 ≤ n := by omega
        simpa only [hnr_xA1, hbr_A1.2.2.2.2.2.2.2.2.2.2.2.2, Nat.add_sub_cancel] using
          execWithin_exactSub (x := x_A1) (d := remReg) (i := numRootsReg) (j := oneP)
            (by rw [hnr_xA1, hbr_A1.2.2.2.2.2.2.2.2.2.2.2.2]; omega)
            (by rw [hnr_xA1, hbr_A1.2.2.2.2.2.2.2.2.2.2.2.2]
                exact hfit_stop.of_le (by simp only [space]; omega))
      have etr2 : ExecWithin (B := .exact) w (.op (.copy iterCur pReg))
          (x_A1.set remReg rtail.length) x_tr 1 := by
        simpa only [x_tr, Data.set_regs, Function.update_of_ne (by decide : pReg ≠ remReg),
          hpr_xA1] using
          (ExecWithin.copy (B := .exact) (w := w) (x := x_A1.set remReg rtail.length)
            (d := iterCur) (s := pReg))
      have hb_tr : x_tr.Bounded w := etr2.bounded (etr1.bounded hb_A1)
      have hbr_tr : BaseRegs n base x_tr :=
        (hbr_A1.set_non_base (by decide) _).set_non_base (by decide) _
      have hst_tr : RawState.ofData n base x_tr = RawState.ofData n base x_A1 := by
        simp only [x_tr, ofData_set_scratch _ (by decide : 17 ≤ iterCur.val),
          ofData_set_scratch _ (by decide : 17 ≤ remReg.val)]
      -- Phase A2 (`x_tr → x_A2`, `rootScatterLoop`)
      have hnd_tr : (forestNodes r_trees ++ (forestNodes slotTrees_1 ++ [z])).Nodup :=
        (perm_swap_front (forestNodes slotTrees_1) (forestNodes r_trees) [z]).nodup_iff.mp hnd_A1
      have hroots_tr : ∀ R ∈ r_trees, ValidRoot (RawState.ofData n base x_tr) none R := by
        intro R hR
        obtain ⟨j, hj, _, hR_eq⟩ := List.mem_eraseIdx_iff_getElem.mp hR
        have hR_st : ValidRoot st none R := hR_eq ▸ hroots _ (List.getElem_mem hj)
        rw [hst_tr]
        refine hR_st.frame_nodes fun u hu => ?_
        have hu_r : u ∈ forestNodes r_trees := mem_forestNodes_iff.mpr ⟨R, hR, hu⟩
        have huz : u ≠ z := fun e => hz_not_cr (List.mem_append_right _ (e ▸ hu_r))
        have ho_u := ho_A1 u (List.mem_append_left _ hu_r)
        exact ⟨hin_A1 ▸ Function.update_of_ne huz _ _, ho_u.2.2.2.2.2, ho_u.2.2.2.2.1,
          ho_u.2.1, hk_A1 ▸ rfl, ho_u.1, ho_u.2.2.1, ho_u.2.2.2.1⟩
      have hchain_all : RightChain st.right (z :: rtail) := hcirc_roots.rightChain
      have hchain_tr : RightChain (RawState.ofData n base x_tr).right rtail := by
        have hch_rt : RightChain st.right rtail := by
          rcases rtail with _ | ⟨_, _⟩
          · trivial
          · exact hchain_all.2
        rw [hst_tr]
        refine hch_rt.frame fun u hu => ?_
        obtain ⟨R, hR, rfl⟩ := List.mem_map.mp (hperm_rtail.subset hu)
        exact (ho_A1 R.root (List.mem_append_left _
          (mem_forestNodes_iff.mpr ⟨R, hR, R.root_mem_nodes⟩))).2.2.2.1
      have hic_tr : ∀ u tl, rtail = u :: tl → x_tr.regs iterCur = u.val := by
        intro u tl hu
        subst hu
        have hrz_u : st.right z = u.val := hchain_all.1
        simp only [x_tr, Data.set_regs, Function.update_self, hrz_u]
      obtain ⟨x_A2, slotTrees_2, maxDeg_2, t_A2, he_A2, ht_A2, hb_A2, hbr_A2, hmod_A2,
        hregs_A2, hmd_A2, hperm_A2, hnd_A2, hs_A2,
        hk_A2, hmk_A2, hin_A2, _, _, hnm_A2, hsz_A2, _⟩ :=
        scatterRootsLoop_exec rtail x_tr r_trees slotTrees_1 [z] z maxDeg_1 hb_tr hbr_tr
          (List.mem_cons_self : z ∈ [z]) hnd_tr (hst_tr ▸ hs_A1) hroots_tr hperm_rtail hchain_tr
          (by simp only [x_tr, Data.set_regs, Function.update_of_ne (by decide : remReg ≠ iterCur),
                Function.update_self])
          (by simp only [x_tr, Data.set_regs,
                Function.update_of_ne (by decide : maxDegReg ≠ iterCur),
                Function.update_of_ne (by decide : maxDegReg ≠ remReg), hmd_A1])
          hic_tr
      rw [hst_tr] at hk_A2 hmk_A2 hin_A2 hnm_A2 hsz_A2
      -- Phase B preamble (`x_A2 → x_B0`, 4 ops)
      have hmd2_log : maxDeg_2 ≤ 2 * Nat.log 2 n + 1 := hs_A2.2.2.2.2.1
      have hmd2_le_n : maxDeg_2 + 1 ≤ n := by
        rcases hs_A2.2.2.2.2.2 with h0 | h2 <;> omega
      let x_B0 := (((x_A2.set minRootReg 0).set numRootsReg 0).set maxDegReg
        (maxDeg_2 + 1)).set curDReg 0
      have eb1 : ExecWithin (B := .exact) w (.op (.copy minRootReg zeroP)) x_A2
          (x_A2.set minRootReg 0) 1 := by
        simpa only [hbr_A2.2.2.2.2.2.2.2.2.2.2.2.1] using
          (ExecWithin.copy (B := .exact) (w := w) (x := x_A2) (d := minRootReg) (s := zeroP))
      have eb2 : ExecWithin (B := .exact) w (.op (.copy numRootsReg zeroP))
          (x_A2.set minRootReg 0) ((x_A2.set minRootReg 0).set numRootsReg 0) 1 := by
        have hz_b : (x_A2.set minRootReg 0).regs zeroP = 0 := hbr_A2.2.2.2.2.2.2.2.2.2.2.2.1
        simpa only [hz_b] using
          (ExecWithin.copy (B := .exact) (w := w) (x := x_A2.set minRootReg 0)
            (d := numRootsReg) (s := zeroP))
      have eb3 : ExecWithin w (.op (.exactBin .add maxDegReg maxDegReg oneP))
          ((x_A2.set minRootReg 0).set numRootsReg 0)
          (((x_A2.set minRootReg 0).set numRootsReg 0).set maxDegReg (maxDeg_2 + 1)) 1 := by
        have hmd_b : ((x_A2.set minRootReg 0).set numRootsReg 0).regs maxDegReg = maxDeg_2 := by
          simp only [Data.set_regs, Function.update_of_ne (by decide : maxDegReg ≠ numRootsReg),
            Function.update_of_ne (by decide : maxDegReg ≠ minRootReg), hmd_A2]
        have ho1_b : ((x_A2.set minRootReg 0).set numRootsReg 0).regs oneP = 1 :=
          hbr_A2.2.2.2.2.2.2.2.2.2.2.2.2
        simpa only [hmd_b, ho1_b] using
          execWithin_exactAdd (x := (x_A2.set minRootReg 0).set numRootsReg 0)
            (d := maxDegReg) (i := maxDegReg) (j := oneP)
            (by rw [hmd_b, ho1_b]; exact hfit_stop.of_le (by simp only [space]; omega))
      have eb4 : ExecWithin (B := .exact) w (.op (.copy curDReg zeroP))
          (((x_A2.set minRootReg 0).set numRootsReg 0).set maxDegReg (maxDeg_2 + 1)) x_B0 1 := by
        have hz_b : (((x_A2.set minRootReg 0).set numRootsReg 0).set maxDegReg
            (maxDeg_2 + 1)).regs zeroP = 0 := hbr_A2.2.2.2.2.2.2.2.2.2.2.2.1
        simpa only [x_B0, hz_b] using
          (ExecWithin.copy (B := .exact) (w := w)
            (x := ((x_A2.set minRootReg 0).set numRootsReg 0).set maxDegReg (maxDeg_2 + 1))
            (d := curDReg) (s := zeroP))
      have hb_B0 : x_B0.Bounded w := eb4.bounded (eb3.bounded (eb2.bounded (eb1.bounded hb_A2)))
      have hbr_B0 : BaseRegs n base x_B0 :=
        (((hbr_A2.set_non_base (by decide) _).set_non_base (by decide) _).set_non_base
          (by decide) _).set_non_base (by decide) _
      have hst_B0 : RawState.ofData n base x_B0 =
          { RawState.ofData n base x_A2 with minRoot := 0, numRoots := 0 } := by
        simp only [x_B0, ofData_set_scratch _ (by decide : 17 ≤ curDReg.val),
          ofData_set_scratch _ (by decide : 17 ≤ maxDegReg.val),
          ofData_set_numRoots, ofData_set_minRoot]
      have hs_B0 : SlotInv n (RawState.ofData n base x_B0) slotTrees_2 maxDeg_2 := by
        rw [hst_B0]
        exact hs_A2.frame rfl fun T hT =>
          (hs_A2.2.1 T hT).1.frame_nodes fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      -- Phase B (`x_B0 → y`, `gatherSlotsLoop`)
      obtain ⟨y, finalRoots, t_B, he_B, ht_B, hb_y, hbr_y, hmod_B, hregs_B,
        hperm_B, hnd_B, hk_B, _, _, _, hmk_B, hin_B, hnm_B, hsz_B,
        hcons_B, hnr_B, hval_B, hrl_B⟩ :=
        gatherSlotsLoop_exec hn_pos (maxDeg_2 + 1) x_B0 0 slotTrees_2 [] z (by omega) hb_B0 hbr_B0
          (by simp only [x_B0, Data.set_regs, Function.update_self])
          (by simp only [x_B0, Data.set_regs,
                Function.update_of_ne (by decide : maxDegReg ≠ curDReg), Function.update_self])
          hs_B0 (fun _ hd => absurd hd (Nat.not_lt_zero _))
          (by simpa only [forestNodes] using hnd_A2)
          (fun _ h => absurd h List.not_mem_nil)
          (by rw [hst_B0]; rfl)
          (Or.inl ⟨rfl, by rw [hst_B0]⟩)
      -- Assemble full `ExecWithin` and total amortized step bound
      let t_else := 13 + t_A1 + 2 + t_A2 + 4 + t_B
      have he_seq :=
        ep1.seq <| execWithin_seq₂ ep2 <| execWithin_seq₂ ep3 <|
          execWithin_seq₃ ep4 <| execWithin_seq₃ ep5 <| execWithin_seq₂ ep6 <|
          he_A1.seq <| etr1.seq <| etr2.seq <| he_A2.seq <|
          eb1.seq <| eb2.seq <| eb3.seq <| eb4.seq he_B
      have he_full : ExecWithin w extractMinCode x y (t_else + 2) := by
        unfold extractMinCode
        exact (ExecWithin.branch_neg hc_top he_seq).mono (by omega)
      have hmod_full : Modifies (Block.mk base (space n)).footprint x.mem y.mem :=
        modifies_block_trans hmod_pre <|
          modifies_block_trans hmod_A1 <|
            modifies_block_trans hmod_A2 hmod_B
      -- Output register values (`outFlag = 1`, `outV = z.val`, `outK = st.key z`)
      have hout_pres : ∀ r : Fin rFib, (r = outFlag ∨ r = outV ∨ r = outK) →
          y.regs r = x_pre.regs r := by
        intro r hr_mem
        have hr30 : r.val < 30 := by rcases hr_mem with rfl | rfl | rfl <;> decide
        have hrm : r ≠ minRootReg := by rcases hr_mem with rfl | rfl | rfl <;> decide
        have hrnr : r ≠ numRootsReg := by rcases hr_mem with rfl | rfl | rfl <;> decide
        have hrnm : r ≠ numMarkedReg := by rcases hr_mem with rfl | rfl | rfl <;> decide
        have hrcd : r ≠ curDReg := by rcases hr_mem with rfl | rfl | rfl <;> decide
        have hrmd : r ≠ maxDegReg := by rcases hr_mem with rfl | rfl | rfl <;> decide
        have hric : r ≠ iterCur := by rcases hr_mem with rfl | rfl | rfl <;> decide
        have hrrem : r ≠ remReg := by rcases hr_mem with rfl | rfl | rfl <;> decide
        rw [hregs_B r hr30 hrm hrnr]
        simp only [x_B0, Data.set_regs, Function.update_of_ne hrcd, Function.update_of_ne hrmd,
          Function.update_of_ne hrnr, Function.update_of_ne hrm]
        rw [hregs_A2 r hr30]
        simp only [x_tr, Data.set_regs, Function.update_of_ne hric, Function.update_of_ne hrrem]
        exact hregs_A1 r hr30 hrnm
      have hy_of : y.regs outFlag = 1 := by
        rw [hout_pres outFlag (Or.inl rfl)]
        simp only [x_pre, p5, p4, p3, p2, Data.set_regs, Data.write_regs,
          Function.update_of_ne (by decide : outFlag ≠ remReg),
          Function.update_of_ne (by decide : outFlag ≠ maxDegReg),
          Function.update_of_ne (by decide : outFlag ≠ pReg),
          Function.update_of_ne (by decide : outFlag ≠ szReg),
          Function.update_of_ne (by decide : outFlag ≠ outK),
          Function.update_of_ne (by decide : outFlag ≠ s0),
          Function.update_of_ne (by decide : outFlag ≠ outV), Function.update_self]
      have hy_ov : y.regs outV = z.val := by
        rw [hout_pres outV (Or.inr (Or.inl rfl))]
        simp only [x_pre, p5, p4, p3, p2, Data.set_regs, Data.write_regs,
          Function.update_of_ne (by decide : outV ≠ remReg),
          Function.update_of_ne (by decide : outV ≠ maxDegReg),
          Function.update_of_ne (by decide : outV ≠ pReg),
          Function.update_of_ne (by decide : outV ≠ szReg),
          Function.update_of_ne (by decide : outV ≠ outK),
          Function.update_of_ne (by decide : outV ≠ s0), Function.update_self]
      have hy_ok : y.regs outK = st.key z := by
        rw [hout_pres outK (Or.inr (Or.inr rfl))]
        simp only [x_pre, p5, p4, p3, Data.set_regs, Data.write_regs,
          Function.update_of_ne (by decide : outK ≠ remReg),
          Function.update_of_ne (by decide : outK ≠ maxDegReg),
          Function.update_of_ne (by decide : outK ≠ pReg),
          Function.update_of_ne (by decide : outK ≠ szReg),
          Function.update_of_ne (by decide : outK ≠ s0), Function.update_self]
      -- Node permutation `(z :: forestNodes finalRoots).Perm (forestNodes ts)`
      have hperm_final_ts : (z :: forestNodes finalRoots).Perm (forestNodes ts) := by
        simp only [forestNodes, List.append_nil] at hperm_B
        have hp_slots : (forestNodes finalRoots).Perm
            (forestNodes c_trees ++ forestNodes r_trees) :=
          hperm_B.trans <| hperm_A2.trans <| List.perm_append_comm.trans (hperm_A1.append_right _)
        have hp_cons : (z :: forestNodes finalRoots).Perm
            ((z :: forestNodes c_trees) ++ forestNodes r_trees) := by
          rw [List.cons_append]
          exact List.Perm.cons z hp_slots
        have hp_ts0 : (T_z.nodes ++ forestNodes r_trees).Perm (forestNodes ts) := hperm_ts
        exact hp_cons.trans (by simpa only [hTz_eq, FHTree.nodes] using hp_ts0)
      -- Final `RawState` equalities
      rw [hst_B0] at hk_B hmk_B hin_B hnm_B hsz_B
      have hk_y : (RawState.ofData n base y).key = st.key := hk_B.trans (hk_A2.trans hk_A1)
      have hin_y : (RawState.ofData n base y).inHeap = Function.update st.inHeap z 0 :=
        hin_B.trans (hin_A2.trans hin_A1)
      have hmk_y : (RawState.ofData n base y).mark = (RawState.ofData n base x_A1).mark :=
        hmk_B.trans hmk_A2
      have hnm_y_eq : (RawState.ofData n base y).numMarked =
          (RawState.ofData n base x_A1).numMarked := hnm_B.trans hnm_A2
      have hsz_y : (RawState.ofData n base y).sz = st.sz - 1 :=
        hsz_B.trans (hsz_A2.trans hsz_A1)
      have hnm_y_mc : (RawState.ofData n base y).numMarked =
          markedCount (RawState.ofData n base y) := by
        rw [hnm_y_eq, hnm_A1]
        exact markedCount_congr fun u => by rw [hin_y, hin_A1, hmk_y]
      refine ⟨y, t_else + 2, he_full, ?_, ?_, hmod_full, ?_⟩
      · simp only [PQCode.decode, code, IndexedMinPQ.spec, hfind, hy_of, hy_ov, hy_ok,
          one_ne_zero, ↓reduceIte, hz_lt, ↓reduceDIte, Fin.eta]
      · simp only [IndexedMinPQ.spec, hfind]
        refine ⟨hb_y, hbr_y, finalRoots, hval_B, (List.nodup_cons.mp hnd_B).2, ?_, ?_, ?_,
          ?_, hnr_B, hnm_y_mc, hcons_B, hrl_B⟩
        · intro v
          by_cases hvz : v = z
          · subst hvz
            simp only [Function.update_self, Option.isSome_none, Bool.false_eq_true, iff_false]
            exact (List.nodup_cons.mp hnd_B).1
          · simp only [Function.update_of_ne hvz, ← hdom v]
            constructor
            · intro hv_f
              exact hperm_final_ts.subset (List.mem_cons_of_mem z hv_f)
            · intro hv_ts
              rcases List.mem_cons.mp (hperm_final_ts.symm.subset hv_ts) with rfl | hv_f
              · exact absurd rfl hvz
              · exact hv_f
        · intro v
          rw [hin_y]
          by_cases hvz : v = z
          · subst hvz
            simp only [Function.update_self, ne_eq, not_true_eq_false, Option.isSome_none,
              Bool.false_eq_true]
            exact ⟨trivial, Nat.zero_le 1⟩
          · simp only [Function.update_of_ne hvz]
            exact hin_iff v
        · intro v kv hsv
          rw [hk_y]
          by_cases hvz : v = z
          · subst hvz; simp only [Function.update_self, reduceCtorEq] at hsv
          · simp only [Function.update_of_ne hvz] at hsv
            exact hkeys v kv hsv
        · rw [hsz_y, hsz, IndexedMinPQ.dom_erase_update, Finset.card_erase_of_mem hz_dom]
      · -- Amortized bound: `(t_else + 2) + potential y ≤ 410 * (Nat.log 2 n + 1) + potential x`
        have hnr_x : x.regs numRootsReg = rtail.length + 1 := by
          change st.numRoots = rtail.length + 1
          omega
        have hnm_x : x.regs numMarkedReg = st.numMarked := rfl
        have hnr_y : y.regs numRootsReg = finalRoots.length := hnr_B
        have hnm_y_le : y.regs numMarkedReg ≤ st.numMarked := by
          change (RawState.ofData n base y).numMarked ≤ st.numMarked
          rw [hnm_y_eq]
          exact hnm_le1
        simp only [potential, unitCredit, slotCredit, List.length_nil, t_else, hnr_x, hnm_x,
          hnr_y] at ht_A1 ht_A2 ht_B ⊢
        omega

end Cslib.Algorithms.WordRAM.PriorityQueue.FibonacciHeap
