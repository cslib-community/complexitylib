/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.DataStructure.PriorityQueue.FibonacciHeap.Basic

/-!
# Fibonacci-heap `decreaseKey` over a record of named cells

`decreaseKey n v k` lowers the key of `v`. If `v` would precede its parent, `cut` moves `v` to the
root list, and `cascade` walks up the ancestors: a marked ancestor is cut in turn, the first
unmarked one is marked [Fredman and Tarjan][FredmanTarjan1987]
[Cormen et al., Section 19.3][CLRS2009]. Then `setKey` stores the key and makes `v` the minimum
root if it precedes it. Cutting before storing the key keeps every tree valid throughout, so no
pre-decrease copy of the state is needed, unlike the hand-stepped `cutNode_forest`.

The proof splits as in `Basic.lean`:

* program evaluation: `wp_unlink`, `wp_toRoot` and `wp_cut` produce the effect `CutsNode` of one
  cut on the raw view (the facts of the hand-stepped `cutNodeCode_raw`); `wp_cascade` runs the
  cascade by induction on its fuel, which exceeds the number of marks; `wp_setKey` and
  `wp_decreaseKey` assemble the three cases (root, no cut, cut);
* forest mathematics on `RawState n` alone: `cutsNode_cutState` (pointer surgery of one cut),
  `CutsNode.cascading` (a cut keeps the forest `Cascading`, the content of `cutNode_forest`),
  `Cascading.clear_root` and `Cascading.mark` (the cascade stops), `Cascading.lowerRootKey` and
  `FibRawInv.lowerKey_noCut` (storing the key), with the existing `ValidSubtree.exists_cut`,
  `ValidSubtree.mark_pending`, `ValidSubtree.lower_key_no_cut` and `CutInv.to_fibRawInv`.

Each cascading cut costs at most `22` record operations and turns a marked non-root into an
unmarked root, which releases `credit = 24`, so the cascade is paid by the potential and
`decreaseKey` costs at most `104` operations amortized.

The module adapts Renfei Zhou's native formalization (`WordRAM/FibonacciHeap`, its `Cut.lean`) to
the record level: his cut (`cutNodeCode_raw`, `cutNode_forest`, with its circular-list uniqueness
argument) and cascading-cut development become `cut`, `CutsNode.cascading`,
`IsCircList.tail_unique` and `cascade`, and his forest lemmas are reused unchanged.

## Main definitions

* `unlink`, `toRoot`, `cut`, `cascade`, `setKey`, `decreaseKey`: record programs.
* `CutsNode`, `cutState`: the effect of one cut on the raw view.
* `Cascading`: the forest during cascading cuts, with one pending ancestor.

## Main results

* `IsCircList.tail_unique`: a circular list is determined by its head.
* `wp_cut`: a cut evaluates to `CutsNode` in at most `20` operations.
* `CutsNode.cascading`: a cut keeps the forest `Cascading`, with the parent pending.
* `wp_cascade`: the cascade costs at most `53` operations plus the potential it releases.
* `wp_decreaseKey`: `decreaseKey` implements `IndexedMinPQ.step` with amortized cost `104`.

## References

* [M. L. Fredman and R. E. Tarjan, *Fibonacci Heaps and Their Uses in Improved Network Optimization
  Algorithms*][FredmanTarjan1987]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Section 19.3][CLRS2009]
-/

@[expose] public section

namespace Cslib.DataStructure.PriorityQueue.FibonacciHeap

open Cslib.WordRAM Cslib.DataStructure Cslib.DataStructure.PriorityQueue
open Cslib.DataStructure.PriorityQueue.WordRAM.FibonacciHeap

/-! ## Programs -/

/-- Unlink `z` from the child list of its parent `p`. -/
def unlink (z p : ℕ) : Prog Unit := do
  let d ← rd (.deg p)
  wr (.deg p) (d - 1)
  if d - 1 = 0 then
    wr (.child p) 0
  else
    let r ← rd (.right z)
    let l ← rd (.left z)
    wr (.left r) l
    wr (.right l) r
    wr (.child p) (r + 1)

/-- Make the unlinked node `z` an unmarked root after the minimum root. -/
def toRoot (z : ℕ) : Prog Unit := do
  let m ← rd .minRoot
  spliceAfter (m - 1) z
  wr (.par z) 0
  let mk ← rd (.mark z)
  wr (.mark z) 0
  let c ← rd .numMarked
  wr .numMarked (c - mk)
  let nr ← rd .numRoots
  wr .numRoots (nr + 1)

/-- Cut `z` from its parent `p`: unlink `z` from `p`'s child list, splice it into the root list
after the minimum root, and clear its parent and mark. -/
def cut (z p : ℕ) : Prog Unit := do
  unlink z p
  toRoot z

/-- Cascading cuts from `z`, which has just lost a child, with at most `fuel` cuts: stop at a
root; mark an unmarked node and stop; cut a marked node and continue with its parent. -/
def cascade : ℕ → ℕ → Prog Unit
  | 0, _ => pure ()
  | fuel + 1, z => do
    let pz ← rd (.par z)
    if pz = 0 then pure ()
    else
      let mk ← rd (.mark z)
      if mk = 0 then
        wr (.mark z) 1
        let c ← rd .numMarked
        wr .numMarked (c + 1)
      else
        cut z (pz - 1)
        cascade fuel (pz - 1)

/-- Store the lowered key `k` of `v`, and make `v` the minimum root if it precedes it. -/
def setKey (v k : ℕ) : Prog Unit := do
  wr (.key v) k
  let m ← rd .minRoot
  let km ← rd (.key (m - 1))
  if IndexedMinPQ.RawPrioLT (v, k) (m - 1, km) then wr .minRoot (v + 1)

/-- Lower the key of `v` to `k` on a heap of `n` handles: if `v` now precedes its parent, cut it
and cascade from the parent; then store the key and update the minimum root. -/
def decreaseKey (n v k : ℕ) : Prog Unit := do
  let pv ← rd (.par v)
  if pv ≠ 0 then
    let kp ← rd (.key (pv - 1))
    if IndexedMinPQ.RawPrioLT (v, k) (pv - 1, kp) then
      cut v (pv - 1)
      cascade (n + 1) (pv - 1)
  setKey v k

/-- The effect of cutting `cur` from its parent `p` when the root list is `m :: rtail`: the facts
of the hand-stepped `cutNodeCode_raw`, on the raw view. -/
structure CutsNode {n : ℕ} (st : RawState n) (cur p m : Fin n) (rtail : List (Fin n))
    (st' : RawState n) : Prop where
  key : st'.key = st.key
  inHeap : st'.inHeap = st.inHeap
  cons : st'.cons = st.cons
  minRoot : st'.minRoot = st.minRoot
  sz : st'.sz = st.sz
  numRoots : st'.numRoots = st.numRoots + 1
  numMarked : st'.numMarked = st.numMarked - st.mark cur
  mark_cur : st'.mark cur = 0
  mark_ne : ∀ u, u ≠ cur → st'.mark u = st.mark u
  deg_p : st'.deg p + 1 = st.deg p
  deg_ne : ∀ u, u ≠ p → st'.deg u = st.deg u
  par_cur : st'.par cur = 0
  par_ne : ∀ u, u ≠ cur → st'.par u = st.par u
  child_ne : ∀ u, u ≠ p → st'.child u = st.child u
  child_one : st.deg p = 1 → st'.child p = 0
  child_two : ∀ (h : Fin n) (tail : List (Fin n)), 2 ≤ st.deg p → st.child p = h.val + 1 →
    IsCircList st.left st.right (h :: tail) → cur ∈ h :: tail →
    ∃ (r : Fin n) (rest : List (Fin n)), st'.child p = r.val + 1 ∧
      IsCircList st'.left st'.right (r :: rest) ∧ (r :: rest).Perm ((h :: tail).erase cur)
  roots : IsCircList st'.left st'.right (m :: cur :: rtail)
  lr_ne : ∀ u, st.par u ≠ p.val + 1 → st.par u ≠ 0 →
    st'.left u = st.left u ∧ st'.right u = st.right u

/-- The state after a cut, given the sibling pointers `left₁`, `right₁` and `p`'s child pointer
`child₁` after unlinking `cur`, and the old right neighbour `r'` of the minimum root `m`. -/
def cutState {n : ℕ} (st : RawState n) (cur p m r' : Fin n) (left₁ right₁ : Fin n → ℕ)
    (child₁ : ℕ) : RawState n :=
  { st with
    deg := Function.update st.deg p (st.deg p - 1)
    child := Function.update st.child p child₁
    left := Function.update (Function.update left₁ cur m.val) r' cur.val
    right := Function.update (Function.update right₁ cur r'.val) m cur.val
    par := Function.update st.par cur 0
    mark := Function.update st.mark cur 0
    numMarked := st.numMarked - st.mark cur
    numRoots := st.numRoots + 1 }

/-- A circular list is determined by its head: from `first`, the `right` pointers trace it. -/
theorem ChainLinks.tail_unique {n : ℕ} {left right : Fin n → ℕ} {first : Fin n} :
    ∀ {prev : Fin n} {t₁ t₂ : List (Fin n)}, (first :: t₁).Nodup → (first :: t₂).Nodup →
      ChainLinks left right first prev t₁ → ChainLinks left right first prev t₂ → t₁ = t₂
  | _, [], [], _, _, _, _ => rfl
  | _, [], b :: _, _, hnd₂, hc₁, hc₂ => by
    have : b = first := Fin.ext (hc₂.1.symm.trans hc₁.1)
    subst this
    exact absurd List.mem_cons_self (List.nodup_cons.mp hnd₂).1
  | _, a :: _, [], hnd₁, _, hc₁, hc₂ => by
    have : a = first := Fin.ext (hc₁.1.symm.trans hc₂.1)
    subst this
    exact absurd List.mem_cons_self (List.nodup_cons.mp hnd₁).1
  | _, a :: t₁, b :: t₂, hnd₁, hnd₂, hc₁, hc₂ => by
    have : a = b := Fin.ext (hc₁.1.symm.trans hc₂.1)
    subst this
    have sub : ∀ {t : List (Fin n)}, (first :: a :: t).Nodup → (first :: t).Nodup := fun h =>
      List.nodup_cons.mpr ⟨fun hm => (List.nodup_cons.mp h).1 (List.mem_cons_of_mem a hm),
        (List.nodup_cons.mp (List.nodup_cons.mp h).2).2⟩
    rw [ChainLinks.tail_unique (sub hnd₁) (sub hnd₂) hc₁.2.2 hc₂.2.2]

/-- A circular list is determined by its head. -/
theorem IsCircList.tail_unique {n : ℕ} {left right : Fin n → ℕ} {h : Fin n}
    {t₁ t₂ : List (Fin n)} (h₁ : IsCircList left right (h :: t₁))
    (h₂ : IsCircList left right (h :: t₂)) : t₁ = t₂ :=
  ChainLinks.tail_unique h₁.1 h₂.1 h₁.2 h₂.2

/-- **The effect of a cut**, from `p`'s child pointer and the sibling pointers after unlinking
`cur` (`hunlink`) and the old right neighbour `r'` of the minimum root `m`. -/
theorem cutsNode_cutState {n : ℕ} {st : RawState n} {cur p m : Fin n} {rtail : List (Fin n)}
    (hdp_pos : 1 ≤ st.deg p)
    (hdp2 : 2 ≤ st.deg p → ∃ (h : Fin n) (tail : List (Fin n)),
      st.child p = h.val + 1 ∧ IsCircList st.left st.right (h :: tail) ∧
      cur ∈ h :: tail ∧ 2 ≤ (h :: tail).length ∧ ∀ u ∈ h :: tail, st.par u = p.val + 1)
    (hcirc_r : IsCircList st.left st.right (m :: rtail))
    (hroots_par0 : ∀ u ∈ m :: rtail, st.par u = 0) (hpar_cur : st.par cur = p.val + 1)
    {left₁ right₁ : Fin n → ℕ} {child₁ : ℕ}
    (hunlink : (st.deg p = 1 ∧ child₁ = 0 ∧ left₁ = st.left ∧ right₁ = st.right) ∨
      (2 ≤ st.deg p ∧ ∃ r l : Fin n, st.right cur = r.val ∧ st.left cur = l.val ∧
        child₁ = r.val + 1 ∧ left₁ = Function.update st.left r l.val ∧
        right₁ = Function.update st.right l r.val))
    {r' : Fin n} (hr' : right₁ m = r'.val) :
    CutsNode st cur p m rtail (cutState st cur p m r' left₁ right₁ child₁) := by
  -- Roots have parent `0`, children of `p` have parent `p + 1`.
  have hroot_ne : ∀ u ∈ m :: rtail, ∀ x, st.par x = p.val + 1 → x ≠ u := fun u hu x hx e => by
    rw [e, hroots_par0 u hu] at hx; omega
  have hcur_roots : cur ∉ m :: rtail := fun hc => hroot_ne cur hc cur hpar_cur rfl
  -- In both cases, the unlinked pointers agree with the old ones at the roots, and at every node
  -- whose parent is not `p`.
  have hframe₁ : ∀ x, st.par x ≠ p.val + 1 → left₁ x = st.left x ∧ right₁ x = st.right x := by
    rcases hunlink with ⟨_, _, rfl, rfl⟩ | ⟨h2, r, l, hr, hl, _, rfl, rfl⟩
    · exact fun _ _ => ⟨rfl, rfl⟩
    · obtain ⟨h, tail, _, hcirc, hcur, hlen, hpar⟩ := hdp2 h2
      obtain ⟨r₂, l₂, _, hr₂, hl₂, hr₂m, hl₂m, -⟩ := hcirc.remove hcur hlen
      obtain rfl : r₂ = r := Fin.ext (hr₂.symm.trans hr)
      obtain rfl : l₂ = l := Fin.ext (hl₂.symm.trans hl)
      intro x hx
      have hxr : x ≠ r₂ := fun e => hx (e ▸ hpar r₂ hr₂m)
      have hxl : x ≠ l₂ := fun e => hx (e ▸ hpar l₂ hl₂m)
      simp [Function.update_of_ne hxr, Function.update_of_ne hxl]
  have hcirc₁ : IsCircList left₁ right₁ (m :: rtail) :=
    hcirc_r.frame fun x hx => hframe₁ x fun e => hroot_ne x hx x e rfl
  have hr'_roots : r' ∈ m :: rtail := by
    obtain ⟨r'', hr'', hmem⟩ := hcirc₁.right_head
    exact (Fin.ext (hr''.symm.trans hr') : r'' = r') ▸ hmem
  have hroots' := hcirc₁.insertAfter hcur_roots hr'
  -- Nodes off the root list and off `p`'s children keep their sibling pointers.
  have hframe : ∀ x, st.par x ≠ p.val + 1 → st.par x ≠ 0 →
      (cutState st cur p m r' left₁ right₁ child₁).left x = st.left x ∧
      (cutState st cur p m r' left₁ right₁ child₁).right x = st.right x := fun x hx hx0 => by
    have hxc : x ≠ cur := fun e => hx (e ▸ hpar_cur)
    have hxm : x ≠ m := fun e => hx0 (e ▸ hroots_par0 m List.mem_cons_self)
    have hxr : x ≠ r' := fun e => hx0 (e ▸ hroots_par0 r' hr'_roots)
    simpa [cutState, Function.update_of_ne hxc, Function.update_of_ne hxm,
      Function.update_of_ne hxr] using hframe₁ x hx
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, by simp [cutState],
    fun u hu => by simp [cutState, hu], by simp [cutState]; omega,
    fun u hu => by simp [cutState, hu], by simp [cutState], fun u hu => by simp [cutState, hu],
    fun u hu => by simp [cutState, hu], fun h1 => ?_, ?_, hroots', hframe⟩
  · rcases hunlink with ⟨_, rfl, _⟩ | ⟨h2, _⟩
    · simp [cutState]
    · omega
  · intro h tail h2 hcp hcirc hcur
    rcases hunlink with ⟨h1, _⟩ | ⟨-, r, l, hr, hl, rfl, rfl, rfl⟩
    · omega
    obtain ⟨h₀, tail₀, hcp₀, hcirc₀, -, hlen₀, hpar₀⟩ := hdp2 h2
    obtain rfl : h₀ = h := Fin.ext (by omega)
    obtain rfl := IsCircList.tail_unique hcirc hcirc₀
    obtain ⟨r₂, l₂, rest, hr₂, hl₂, -, -, -, hcirc₂, hperm₂⟩ := hcirc.remove hcur hlen₀
    obtain rfl : r₂ = r := Fin.ext (hr₂.symm.trans hr)
    obtain rfl : l₂ = l := Fin.ext (hl₂.symm.trans hl)
    refine ⟨r₂, rest, by simp [cutState], hcirc₂.frame fun x hx => ?_, hperm₂⟩
    have hx_er := hperm₂.subset hx
    have hxc : x ≠ cur := fun e => by subst e; exact hcirc.1.not_mem_erase hx_er
    have hpx := hpar₀ x (List.mem_of_mem_erase hx_er)
    simp [cutState, Function.update_of_ne hxc,
      Function.update_of_ne (hroot_ne m List.mem_cons_self x hpx),
      Function.update_of_ne (hroot_ne r' hr'_roots x hpx)]

/-! ## Forest mathematics of cascading cuts -/

/-- The forest during cascading cuts from `v`: `FibRawInv` with one `pending` ancestor that may
have lost a child, and with the minimum-root comparison waived for `v`. With `v` a root, this is
the existing `CutInv`. -/
structure Cascading (n K : ℕ) (s : IndexedMinPQ.State n) (st : RawState n) (v m : Fin n)
    (pending : Option (Fin n)) (ts : List (FHTree n)) : Prop where
  valid : ∀ T ∈ ts, ValidRoot st pending T
  nodup : (forestNodes ts).Nodup
  dom : ∀ u, u ∈ forestNodes ts ↔ (s u).isSome
  inHeap : ∀ u, (st.inHeap u ≠ 0 ↔ (s u).isSome) ∧ st.inHeap u ≤ 1
  keys : ∀ u ku, s u = some ku → st.key u = ku ∧ ku ≤ K
  sz : st.sz = (IndexedMinPQ.dom s).card
  numRoots : st.numRoots = ts.length
  numMarked : st.numMarked = markedCount st
  cons : ∀ d ≤ n, st.cons d = 0
  minRoot : st.minRoot = m.val + 1
  roots : ∃ rtail, IsCircList st.left st.right (m :: rtail) ∧ (m :: rtail).Perm (ts.map FHTree.root)
  min_le : ∀ T ∈ ts, T.root ≠ v → IndexedMinPQ.PrioLE (m, st.key m) (T.root, st.key T.root)

/-- With `v` a root, `Cascading` is the existing `CutInv`. -/
theorem Cascading.cutInv {n K : ℕ} {s : IndexedMinPQ.State n} {st : RawState n} {v m : Fin n}
    {pending : Option (Fin n)} {ts : List (FHTree n)} (h : Cascading n K s st v m pending ts)
    (hv : ∃ T ∈ ts, T.root = v) : CutInv n K s st v m pending := by
  obtain ⟨rtail, hcirc, hperm⟩ := h.roots
  exact ⟨ts, h.valid, h.nodup, h.dom, h.inHeap, h.keys, h.sz, h.numRoots, h.numMarked, h.cons,
    ⟨rtail, h.minRoot, hcirc, hperm⟩, hv, h.min_le⟩

/-- A valid heap is `Cascading` with nothing pending. -/
theorem cascading_of_fibRawInv {n K : ℕ} {s : IndexedMinPQ.State n} {st : RawState n} {v : Fin n}
    (h : FibRawInv n K s st) (hv : (s v).isSome) :
    ∃ m ts, Cascading n K s st v m none ts := by
  obtain ⟨ts, hts, hnd, hdom, hin, hkeys, hsz, hnr, hnm, hcons, hrl⟩ := h
  rcases hrl with ⟨rfl, _⟩ | ⟨m, rtail, hm, hcirc, hperm, hle⟩
  · exact absurd ((hdom v).mpr hv) List.not_mem_nil
  · exact ⟨m, ts, ⟨hts, hnd, hdom, hin, hkeys, hsz, hnr, hnm, hcons, hm, ⟨rtail, hcirc, hperm⟩,
      fun T hT _ => hle T hT⟩⟩

/-- In a valid subtree with distinct nodes, every node has fewer children than the tree has
nodes. -/
theorem ValidSubtree.deg_lt_length {n : ℕ} {st : RawState n} {pending : Option (Fin n)}
    {T : FHTree n} (hT : ValidSubtree st pending T) (hnd : T.nodes.Nodup) {x : Fin n}
    (hx : x ∈ T.nodes) : st.deg x < T.nodes.length := by
  induction hT with
  | @mk u cs _ _ hdeg _ _ _ _ _ ih =>
    have hlen : (FHTree.node u cs).nodes.length = (forestNodes cs).length + 1 := by
      simp [FHTree.nodes]
    rw [hlen]
    rcases List.mem_cons.mp hx with rfl | hx
    · have := forestNodes_length_ge cs
      omega
    · obtain ⟨c, hc, hxc⟩ := mem_forestNodes_iff.mp hx
      have hnd_c := forestNodes_nodup_tree (List.nodup_cons.mp hnd).2 hc
      have := ih c hc hnd_c hxc
      obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hc
      have : c.nodes.length ≤ (forestNodes (l₁ ++ c :: l₂)).length := by
        simp only [forestNodes_append, forestNodes, List.length_append]
        omega
      omega

/-- **A cut keeps the forest `Cascading`**, with the parent `p` now pending. The cut node `cur`
becomes the root of a new tree; its old tree loses that subtree. This is the forest part of the
hand-stepped `cutNode_forest`. -/
theorem CutsNode.cascading {n K : ℕ} {s : IndexedMinPQ.State n} {st st' : RawState n}
    {cur p v m : Fin n} {pending : Option (Fin n)} {ts : List (FHTree n)} {rtail : List (Fin n)}
    (h : Cascading n K s st v m pending ts) (hperm_r : (m :: rtail).Perm (ts.map FHTree.root))
    (hpend : pending = none ∨ pending = some cur)
    (hv_root : cur = v ∨ ∃ T ∈ ts, T.root = v)
    (hcur_ne_v : ∀ T ∈ ts, cur ∈ T.nodes → T.root ≠ v)
    (hcur : cur ∈ forestNodes ts) (hpar_cur : st.par cur = p.val + 1)
    (hcut : CutsNode st cur p m rtail st') :
    ∃ ts', Cascading n K s st' v m (some p) ts' ∧ (∃ T ∈ ts', T.root = v) ∧
      (∀ T ∈ ts', p ∈ T.nodes → T.root ≠ v) ∧ p ∈ forestNodes ts' := by
  obtain ⟨Ti, hTi, hcur_Ti⟩ := mem_forestNodes_iff.mp hcur
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hTi
  have hnd_Ti : (ts[i]).nodes.Nodup := forestNodes_nodup_tree h.nodup hTi
  have hTi_ne_v : (ts[i]).root ≠ v := hcur_ne_v _ hTi hcur_Ti
  have hcur_ne_root : cur ≠ (ts[i]).root := fun e => by
    have := (h.valid _ hTi).2.1
    rw [← e] at this
    omega
  have hcur_desc : cur ∈ forestNodes (ts[i]).children := by
    rw [(ts[i]).nodes_eq] at hcur_Ti
    exact (List.mem_cons.mp hcur_Ti).resolve_left hcur_ne_root
  obtain ⟨T_cut, T', hcut_r, hT'_r, hp_T', hperm_Ti, hvalid_cut, hvalid_T'⟩ :=
    (h.valid _ hTi).1.exists_cut hnd_Ti hcur_desc hpar_cur hpend
      (fun u _ => ⟨congrFun hcut.inHeap u, congrFun hcut.key u⟩)
      ⟨hcut.mark_cur, fun u _ hu => hcut.mark_ne u hu⟩
      ⟨hcut.deg_p, fun u _ hu => hcut.deg_ne u hu⟩
      ⟨hcut.par_cur, fun u _ hu => hcut.par_ne u hu⟩
      ⟨hcut.child_one, hcut.child_two⟩
      (fun u _ hu => hcut.child_ne u hu) (fun u _ h1 h0 => hcut.lr_ne u h1 h0)
  have hnd_cut_T' : (T_cut.nodes ++ T'.nodes).Nodup := hperm_Ti.nodup_iff.mpr hnd_Ti
  have hcur_T' : cur ∉ T'.nodes := fun hm =>
    (List.nodup_append.mp hnd_cut_T').2.2 cur (hcut_r ▸ T_cut.root_mem_nodes) cur hm rfl
  have hT'_ne_cur : T'.root ≠ cur := fun e => hcur_T' (e ▸ T'.root_mem_nodes)
  let ts' : List (FHTree n) := T_cut :: ts.set i T'
  have hperm_fn : (forestNodes ts').Perm (forestNodes ts) :=
    forestNodes_set_perm ts i hi T_cut T' hperm_Ti
  have hnd' : (forestNodes ts').Nodup := hperm_fn.nodup_iff.mpr h.nodup
  have hT'_mem : T' ∈ ts' := List.mem_cons_of_mem _ (List.mem_iff_getElem.mpr
    ⟨i, by simpa using hi, by simp⟩)
  -- Every other tree is untouched: none of its nodes is `cur` or `p`.
  have hother : ∀ j (hj : j < ts.length), j ≠ i → ValidRoot st' (some p) ts[j] := by
    intro j hj hji
    have hcur_j : cur ∉ (ts[j]).nodes := fun hm =>
      forestNodes_nodup_idx_disjoint h.nodup hi hj (Ne.symm hji) hcur_Ti hm
    have hp_j : p ∉ (ts[j]).nodes := fun hm => by
      have hp_Ti : p ∈ (ts[i]).nodes := hperm_Ti.subset (List.mem_append_right _ hp_T')
      exact forestNodes_nodup_idx_disjoint h.nodup hi hj (Ne.symm hji) hp_Ti hm
    have hsub : ValidSubtree st none ts[j] := by
      rcases hpend with rfl | rfl
      · exact (h.valid _ (List.getElem_mem hj)).1
      · exact (h.valid _ (List.getElem_mem hj)).1.clear_pending fun hm =>
          hcur_j ((ts[j]).nodes_eq ▸ List.mem_cons_of_mem _ hm)
    have hr_ne : (ts[j]).root ≠ cur := fun e => hcur_j (e ▸ (ts[j]).root_mem_nodes)
    refine ⟨(hsub.frame (pending' := none) (fun u hu => ?_) (fun u hu => ?_)).weaken_pending _,
      by rw [hcut.par_ne _ hr_ne]; exact (h.valid _ (List.getElem_mem hj)).2.1,
      by rw [hcut.mark_ne _ hr_ne]; exact (h.valid _ (List.getElem_mem hj)).2.2⟩
    · have hu_cur : u ≠ cur := fun e => hcur_j (e ▸ hu)
      have hu_p : u ≠ p := fun e => hp_j (e ▸ hu)
      exact ⟨congrFun hcut.inHeap u, hcut.mark_ne u hu_cur, hcut.deg_ne u hu_p,
        hcut.child_ne u hu_p, congrFun hcut.key u⟩
    · have hu_j : u ∈ (ts[j]).nodes := (ts[j]).nodes_eq ▸ List.mem_cons_of_mem _ hu
      have hu_cur : u ≠ cur := fun e => hcur_j (e ▸ hu_j)
      obtain ⟨q, hq, hpq⟩ := hsub.par_of_mem_children u hu
      have hqp : q ≠ p := fun e => hp_j (e ▸ hq)
      have hlr := hcut.lr_ne u (by rw [hpq]; have := Fin.val_ne_of_ne hqp; omega)
        (by rw [hpq]; omega)
      exact ⟨hcut.par_ne u hu_cur, hlr.1, hlr.2, Iff.rfl⟩
  have hvalid' : ∀ T ∈ ts', ValidRoot st' (some p) T := by
    intro T hT
    rcases List.mem_cons.mp hT with rfl | hT
    · exact ⟨hvalid_cut.1.weaken_pending _, hvalid_cut.2.1, hvalid_cut.2.2⟩
    · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hT
      have hj' : j < ts.length := by simpa using hj
      by_cases hji : j = i
      · subst hji
        simp only [List.getElem_set_self]
        refine ⟨hvalid_T', ?_, ?_⟩
        · rw [hcut.par_ne _ hT'_ne_cur, hT'_r]; exact (h.valid _ hTi).2.1
        · rw [hcut.mark_ne _ hT'_ne_cur, hT'_r]; exact (h.valid _ hTi).2.2
      · rw [List.getElem_set_ne (Ne.symm hji)]
        exact hother j hj' hji
  have hroots' : (m :: cur :: rtail).Perm (ts'.map FHTree.root) := by
    simp only [ts', List.map_cons, hcut_r, map_root_set_eq ts i hi T' hT'_r]
    exact (List.Perm.swap cur m rtail).trans (List.Perm.cons cur hperm_r)
  have hmem_set : ∀ j (hj : j < ts.length), j ≠ i → ts[j] ∈ ts' := fun j hj hji =>
    List.mem_cons_of_mem _ (List.mem_iff_getElem.mpr ⟨j, by simpa using hj,
      by simp [List.getElem_set_ne (Ne.symm hji)]⟩)
  refine ⟨ts', ⟨hvalid', hnd', fun u => hperm_fn.mem_iff.trans (h.dom u),
    fun u => by rw [hcut.inHeap]; exact h.inHeap u,
    fun u ku hu => by rw [hcut.key]; exact h.keys u ku hu, hcut.sz.trans h.sz,
    by rw [hcut.numRoots, h.numRoots]; simp [ts'], ?_,
    fun d hd => by rw [hcut.cons]; exact h.cons d hd,
    hcut.minRoot.trans h.minRoot, ⟨cur :: rtail, hcut.roots, hroots'⟩, ?_⟩, ?_, ?_,
    mem_forestNodes_iff.mpr ⟨T', hT'_mem, hp_T'⟩⟩
  · -- The cut node loses its mark, if any.
    obtain ⟨-, -, -, hin_cur, hmk_cur, -⟩ := exists_parent_info (h.valid _ hTi).1 hcur_desc hpar_cur
    rw [hcut.numMarked, h.numMarked]
    have hiff : ∀ x, x ≠ cur → ((st'.inHeap x ≠ 0 ∧ st'.mark x ≠ 0) ↔
        (st.inHeap x ≠ 0 ∧ st.mark x ≠ 0)) := fun x hx => by
      rw [hcut.inHeap, hcut.mark_ne x hx]
    by_cases hm0 : st.mark cur = 0
    · rw [hm0, Nat.sub_zero]
      refine (markedCount_congr fun x => ?_).symm
      by_cases hx : x = cur
      · subst hx; simp [hcut.mark_cur, hm0]
      · exact hiff x hx
    · have := markedCount_clear_one hin_cur hm0 hcut.mark_cur hiff
      omega
  · intro T hT hTv
    rw [hcut.key]
    rcases List.mem_cons.mp hT with rfl | hT
    · rw [hcut_r] at hTv ⊢
      exact (h.min_le _ hTi hTi_ne_v).trans ((h.valid _ hTi).1.prioLE_of_mem hcur_Ti)
    · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hT
      have hj' : j < ts.length := by simpa using hj
      by_cases hji : j = i
      · subst hji
        simp only [List.getElem_set_self, hT'_r] at hTv ⊢
        exact h.min_le _ hTi hTi_ne_v
      · simp only [List.getElem_set_ne (Ne.symm hji)] at hTv ⊢
        exact h.min_le _ (List.getElem_mem hj') hTv
  · rcases hv_root with rfl | ⟨Tv, hTv, hTv_r⟩
    · exact ⟨T_cut, List.mem_cons_self, hcut_r⟩
    · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hTv
      have hji : j ≠ i := fun e => by subst e; exact hTi_ne_v hTv_r
      exact ⟨_, hmem_set j hj hji, hTv_r⟩
  · intro T hT hpT
    by_cases hTT' : T = T'
    · subst hTT'; rw [hT'_r]; exact hTi_ne_v
    · exact (forestNodes_nodup_disjoint hnd' hT hT'_mem hTT' hpT hp_T').elim

/-- A node of the forest with a parent `p` is a strict descendant of its tree. -/
theorem Cascading.desc_of_par {n K : ℕ} {s : IndexedMinPQ.State n} {st : RawState n}
    {v m : Fin n} {pending : Option (Fin n)} {ts : List (FHTree n)}
    (h : Cascading n K s st v m pending ts) {z : Fin n} (hz : z ∈ forestNodes ts)
    (hpz : st.par z ≠ 0) : ∃ T ∈ ts, z ∈ forestNodes T.children := by
  obtain ⟨T, hT, hzT⟩ := mem_forestNodes_iff.mp hz
  refine ⟨T, hT, ?_⟩
  rw [T.nodes_eq] at hzT
  exact (List.mem_cons.mp hzT).resolve_left fun e => hpz (e ▸ (h.valid T hT).2.1)

/-- **The preconditions of a cut** of a non-root `cur` from its parent `p`, as `wp_cut` takes
them. -/
theorem Cascading.cut_pre {n K : ℕ} {s : IndexedMinPQ.State n} {st : RawState n}
    {v m : Fin n} {pending : Option (Fin n)} {ts : List (FHTree n)} {rtail : List (Fin n)}
    (h : Cascading n K s st v m pending ts) (hperm_r : (m :: rtail).Perm (ts.map FHTree.root))
    {cur p : Fin n} (hcur : cur ∈ forestNodes ts) (hpar_cur : st.par cur = p.val + 1) :
    1 ≤ st.deg p ∧
    (2 ≤ st.deg p → ∃ (h : Fin n) (tail : List (Fin n)),
      st.child p = h.val + 1 ∧ IsCircList st.left st.right (h :: tail) ∧
      cur ∈ h :: tail ∧ 2 ≤ (h :: tail).length ∧ ∀ u ∈ h :: tail, st.par u = p.val + 1) ∧
    st.deg p ≤ n ∧ (∀ u ∈ m :: rtail, st.par u = 0) ∧ st.numRoots + 1 ≤ n ∧
    st.numMarked ≤ n := by
  obtain ⟨T, hT, hdesc⟩ := h.desc_of_par hcur (by omega)
  obtain ⟨hpT, -, -, -, -, hdp, hdp2⟩ := exists_parent_info (h.valid T hT).1 hdesc hpar_cur
  have hnd_T := forestNodes_nodup_tree h.nodup hT
  have hdeg := ValidSubtree.deg_lt_length (h.valid T hT).1 hnd_T hpT
  have hlen : T.nodes.length ≤ n := by simpa using hnd_T.length_le_card
  have hroot0 : ∀ u ∈ ts.map FHTree.root, st.par u = 0 := fun u hu => by
    obtain ⟨R, hR, rfl⟩ := List.mem_map.mp hu
    exact (h.valid R hR).2.1
  have hcur_roots : cur ∉ ts.map FHTree.root := fun hm => by
    have := hroot0 cur hm
    omega
  have hnd_roots : (cur :: ts.map FHTree.root).Nodup :=
    List.nodup_cons.mpr ⟨hcur_roots, map_root_nodup h.nodup⟩
  have hnr : (cur :: ts.map FHTree.root).length ≤ n := by simpa using hnd_roots.length_le_card
  simp only [List.length_cons, List.length_map] at hnr
  refine ⟨hdp, hdp2, by omega, fun u hu => hroot0 u (hperm_r.subset hu), by rw [h.numRoots]; omega,
    h.numMarked ▸ markedCount_le_n st⟩

/-- **The cascade stops at a root**: a pending root has lost nothing that matters. -/
theorem Cascading.clear_root {n K : ℕ} {s : IndexedMinPQ.State n} {st : RawState n}
    {v m z : Fin n} {ts : List (FHTree n)} (h : Cascading n K s st v m (some z) ts)
    (hz : z ∈ forestNodes ts) (hpz : st.par z = 0) : Cascading n K s st v m none ts := by
  obtain ⟨Tz, hTz, hzT⟩ := mem_forestNodes_iff.mp hz
  have hz_root : z = Tz.root := ((h.valid Tz hTz).par_eq_zero_iff_root hzT).mp hpz
  refine { h with valid := fun T hT => ⟨(h.valid T hT).1.clear_pending fun hm => ?_,
    (h.valid T hT).2.1, (h.valid T hT).2.2⟩ }
  exact descendant_ne_root_of_nodup h.nodup hT hTz hm hz_root

/-- **The cascade stops at an unmarked node**, which it marks. -/
theorem Cascading.mark {n K : ℕ} {s : IndexedMinPQ.State n} {st : RawState n}
    {v m z : Fin n} {ts : List (FHTree n)} (h : Cascading n K s st v m (some z) ts)
    (hz : z ∈ forestNodes ts) (hpz : st.par z ≠ 0) (hmz : st.mark z = 0) :
    Cascading n K s { st with
      mark := Function.update st.mark z 1
      numMarked := st.numMarked + 1 } v m none ts := by
  obtain ⟨Tz, hTz, hdesc⟩ := h.desc_of_par hz hpz
  have hzT : z ∈ Tz.nodes := Tz.nodes_eq ▸ List.mem_cons_of_mem _ hdesc
  have hz_ne_root : ∀ T ∈ ts, T.root ≠ z := fun T hT e =>
    descendant_ne_root_of_nodup h.nodup hTz hT hdesc e.symm
  refine { h with valid := fun T hT => ⟨?_, (h.valid T hT).2.1, ?_⟩, numMarked := ?_ }
  · by_cases hTT : T = Tz
    · subst hTT
      exact (h.valid T hT).1.mark_pending hmz (by simp)
        (fun x _ hx => by simp [Function.update_of_ne hx]) (fun _ _ => ⟨rfl, rfl, rfl, rfl⟩)
        (fun _ _ => ⟨rfl, rfl, rfl⟩)
    · have hzT' : z ∉ T.nodes := fun hm => forestNodes_nodup_disjoint h.nodup hT hTz hTT hm hzT
      exact ((h.valid T hT).1.clear_pending fun hm => hzT' (T.nodes_eq ▸ List.mem_cons_of_mem _ hm)
        ).frame (fun x hx => ⟨rfl, by
          simp [Function.update_of_ne (fun e : x = z => hzT' (e ▸ hx))], rfl, rfl, rfl⟩)
        (fun _ _ => ⟨rfl, rfl, rfl, Iff.rfl⟩)
  · simpa [Function.update_of_ne (hz_ne_root T hT)] using (h.valid T hT).2.2
  · obtain ⟨T, hT, hzT⟩ := mem_forestNodes_iff.mp hz
    have hin_z : st.inHeap z ≠ 0 := ((h.inHeap z).1).mpr ((h.dom z).mp hz)
    rw [h.numMarked]
    exact (markedCount_set_one (st := st)
      (st' := { st with mark := Function.update st.mark z 1, numMarked := st.numMarked + 1 })
      hin_z hmz (by simp) fun x hx => by simp [Function.update_of_ne hx]).symm

/-- **Lowering the key of the root `v`** keeps every tree valid, and with `v` a root the forest
satisfies the existing `CutInv`, ready for the minimum-root update. -/
theorem Cascading.lowerRootKey {n K : ℕ} {s : IndexedMinPQ.State n} {st : RawState n}
    {v m : Fin n} {ts : List (FHTree n)} (h : Cascading n K s st v m none ts)
    (hv : ∃ T ∈ ts, T.root = v) {k₀ k : ℕ} (hsv : s v = some k₀) (hk₀ : k ≤ k₀) (hK : k ≤ K) :
    CutInv n K (Function.update s v (some k)) { st with key := Function.update st.key v k }
      v m none := by
  obtain ⟨Tv, hTv, rfl⟩ := hv
  have hkv : st.key Tv.root = k₀ := (h.keys _ k₀ hsv).1
  have hvalid : ∀ T ∈ ts, ValidRoot { st with key := Function.update st.key Tv.root k } none T := by
    intro T hT
    by_cases hTT : T = Tv
    · subst hTT
      refine ⟨(h.valid T hT).1.lower_key_no_cut (k := k) (forestNodes_nodup_tree h.nodup hT)
        T.root_mem_nodes (by omega) (by simp) (fun x _ hx => by simp [hx])
        (fun _ _ => ⟨rfl, rfl, rfl, rfl⟩) (fun _ _ => ⟨rfl, rfl, rfl⟩) (Or.inl rfl),
        (h.valid T hT).2.1, (h.valid T hT).2.2⟩
    · have hv_T : Tv.root ∉ T.nodes := fun hm => forestNodes_nodup_disjoint h.nodup hT hTv hTT hm
        Tv.root_mem_nodes
      exact (h.valid T hT).frame_tree (fun x hx => ⟨rfl, rfl, rfl, rfl,
        by simp [Function.update_of_ne (fun e : x = Tv.root => hv_T (e ▸ hx))], rfl⟩)
        (fun _ _ => ⟨rfl, rfl⟩)
  have hsome : ∀ u, (Function.update s Tv.root (some k) u).isSome = (s u).isSome := fun u => by
    by_cases hu : u = Tv.root
    · subst hu; simp [hsv]
    · simp [hu]
  obtain ⟨rtail, hcirc, hperm⟩ := h.roots
  refine ⟨ts, hvalid, h.nodup, fun u => (h.dom u).trans (by rw [hsome]),
    fun u => by rw [hsome]; exact h.inHeap u, fun u ku hu => ?_, ?_, h.numRoots,
    h.numMarked.trans (markedCount_congr fun _ => Iff.rfl).symm, h.cons,
    ⟨rtail, h.minRoot, hcirc, hperm⟩, ⟨Tv, hTv, rfl⟩, fun T hT hTr => ?_⟩
  · by_cases hu' : u = Tv.root
    · subst hu'
      simp only [Function.update_self, Option.some.injEq] at hu
      subst hu
      simp [hK]
    · rw [Function.update_of_ne hu'] at hu
      simpa [hu'] using h.keys u ku hu
  · rw [h.sz, IndexedMinPQ.dom_decreaseKey (IndexedMinPQ.mem_dom_iff.mpr ⟨k₀, hsv⟩)]
  · have hle := h.min_le T hT hTr
    simp only [Function.update_of_ne hTr]
    by_cases hmv : m = Tv.root
    · subst hmv
      simp only [Function.update_self]
      refine IndexedMinPQ.PrioLE.trans ?_ hle
      dsimp only [IndexedMinPQ.PrioLE, IndexedMinPQ.RawPrioLE]
      omega
    · simpa [Function.update_of_ne hmv] using hle

/-- **Lowering a key without a cut.** If `v` keeps its heap order with its parent `p`, the heap
stays valid, and `v` cannot precede the minimum root. -/
theorem FibRawInv.lowerKey_noCut {n K : ℕ} {s : IndexedMinPQ.State n} {st : RawState n}
    {v p : Fin n} {k₀ k : ℕ} (h : FibRawInv n K s st) (hsv : s v = some k₀) (hk₀ : k ≤ k₀)
    (hK : k ≤ K) (hpv : st.par v = p.val + 1) (hord : ¬IndexedMinPQ.PrioLT (v, k) (p, st.key p)) :
    FibRawInv n K (Function.update s v (some k)) { st with key := Function.update st.key v k } ∧
      ∀ m : Fin n, st.minRoot = m.val + 1 →
        ¬IndexedMinPQ.PrioLT (v, k) (m, Function.update st.key v k m) := by
  obtain ⟨m, ts, hc⟩ := cascading_of_fibRawInv (v := v) h (by simp [hsv])
  obtain ⟨Tv, hTv, hvT⟩ := mem_forestNodes_iff.mp ((hc.dom v).mpr (by simp [hsv]))
  have hkv : st.key v = k₀ := (hc.keys v k₀ hsv).1
  have hv_ne_root : ∀ T ∈ ts, T.root ≠ v := fun T hT e => by
    have := (hc.valid T hT).2.1
    rw [e] at this
    omega
  let st₁ : RawState n := { st with key := Function.update st.key v k }
  have hvalid : ∀ T ∈ ts, ValidRoot st₁ none T := by
    intro T hT
    by_cases hTT : T = Tv
    · subst hTT
      exact ⟨(hc.valid T hT).1.lower_key_no_cut (k := k) (forestNodes_nodup_tree hc.nodup hT) hvT
        (by omega) (by simp [st₁]) (fun x _ hx => by simp [st₁, hx])
        (fun _ _ => ⟨rfl, rfl, rfl, rfl⟩) (fun _ _ => ⟨rfl, rfl, rfl⟩) (Or.inr ⟨p, hpv, hord⟩),
        (hc.valid T hT).2.1, (hc.valid T hT).2.2⟩
    · have hv_T : v ∉ T.nodes := fun hm => forestNodes_nodup_disjoint hc.nodup hT hTv hTT hm hvT
      exact (hc.valid T hT).frame_tree (fun x hx => ⟨rfl, rfl, rfl, rfl,
        by simp [st₁, Function.update_of_ne (fun e : x = v => hv_T (e ▸ hx))], rfl⟩)
        (fun _ _ => ⟨rfl, rfl⟩)
  have hroot_key : ∀ T ∈ ts, st₁.key T.root = st.key T.root := fun T hT => by
    simp [st₁, Function.update_of_ne (hv_ne_root T hT)]
  obtain ⟨rtail, hcirc, hperm⟩ := hc.roots
  obtain ⟨Tm, hTm, hTm_r⟩ := List.mem_map.mp (hperm.subset List.mem_cons_self)
  have hmv : m ≠ v := hTm_r ▸ hv_ne_root Tm hTm
  have hcut : CutInv n K (Function.update s v (some k)) st₁ Tv.root m none := by
    have hsome : ∀ u, (Function.update s v (some k) u).isSome = (s u).isSome := fun u => by
      by_cases hu : u = v
      · subst hu; simp [hsv]
      · simp [hu]
    refine ⟨ts, hvalid, hc.nodup, fun u => (hc.dom u).trans (by rw [hsome]),
      fun u => by rw [hsome]; exact hc.inHeap u, fun u ku hu => ?_, ?_, hc.numRoots,
      hc.numMarked.trans (markedCount_congr fun _ => Iff.rfl).symm, hc.cons,
      ⟨rtail, hc.minRoot, hcirc, hperm⟩, ⟨Tv, hTv, rfl⟩, fun T hT _ => ?_⟩
    · by_cases hu' : u = v
      · subst hu'
        simp only [Function.update_self, Option.some.injEq] at hu
        subst hu
        simp [st₁, hK]
      · rw [Function.update_of_ne hu'] at hu
        simpa [st₁, hu'] using hc.keys u ku hu
    · rw [hc.sz, IndexedMinPQ.dom_decreaseKey (IndexedMinPQ.mem_dom_iff.mpr ⟨k₀, hsv⟩)]
    · rw [hroot_key T hT, ← hTm_r, hroot_key Tm hTm, hTm_r]
      by_cases hTv' : T.root = v
      · exact (hv_ne_root T hT hTv').elim
      · exact hc.min_le T hT hTv'
  -- `m` precedes the root of `v`'s tree, which precedes `v`.
  have hmin_v : IndexedMinPQ.PrioLE (m, st₁.key m) (v, k) := by
    have h1 := hc.min_le Tv hTv (hv_ne_root Tv hTv)
    have h2 := (hvalid Tv hTv).1.prioLE_of_mem hvT
    rw [← hroot_key Tv hTv, ← hTm_r, ← hroot_key Tm hTm, hTm_r] at h1
    simpa [st₁] using h1.trans h2
  refine ⟨CutInv.to_fibRawInv hcut ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    (Or.inr ⟨fun hlt => ?_, hc.minRoot⟩), fun m' hm' => ?_⟩
  · have hle := hc.min_le Tv hTv (hv_ne_root Tv hTv)
    rw [← hroot_key Tv hTv, ← hTm_r, ← hroot_key Tm hTm, hTm_r] at hle
    exact IndexedMinPQ.not_prioLT_iff_prioLE.mpr hle hlt
  · obtain rfl : m' = m := Fin.ext (by have := hc.minRoot; omega)
    exact IndexedMinPQ.not_prioLT_iff_prioLE.mpr hmin_v

section Programs

variable {n w : ℕ}

/-- Splicing `u` after `h`, whose right neighbour is `r`, makes four writes. -/
theorem wp_spliceAfter {g : Cell → ℕ} {h u r : Fin n} (hr : (view n g).right h = r.val)
    (hfit : Fits w n) {Q : Unit → (Cell → ℕ) → ℕ → Prop}
    (hQ : Q () (Function.update (Function.update (Function.update (Function.update g
      (.left u) h) (.left r) u) (.right u) r) (.right h) u) 5) :
    Record.wp (Cell.ok n) w (spliceAfter h u) Q g := by
  have hr' : g (.right h) = r.val := hr
  simp only [spliceAfter, Record.wp_read_bind, Record.wp_write_bind, Record.wp_write, hr',
    Cell.ok]
  exact ⟨h.isLt, ⟨u.isLt, hfit.of_le h.isLt.le⟩, ⟨r.isLt, hfit.of_le u.isLt.le⟩,
    ⟨u.isLt, hfit.of_le r.isLt.le⟩, ⟨h.isLt, hfit.of_le u.isLt.le⟩, hQ⟩

/-- Unlinking `cur` from `p`'s children evaluates to the two cases of `cutsNode_cutState`. -/
theorem wp_unlink {g : Cell → ℕ} {cur p : Fin n}
    (hdp_pos : 1 ≤ (view n g).deg p)
    (hdp2 : 2 ≤ (view n g).deg p → ∃ (h : Fin n) (tail : List (Fin n)),
      (view n g).child p = h.val + 1 ∧ IsCircList (view n g).left (view n g).right (h :: tail) ∧
      cur ∈ h :: tail ∧ 2 ≤ (h :: tail).length ∧ ∀ u ∈ h :: tail, (view n g).par u = p.val + 1)
    (hdp_le : (view n g).deg p ≤ n) (hfit : Fits w n) {Q : Unit → (Cell → ℕ) → ℕ → Prop}
    (hQ : ∀ g' t, t ≤ 7 → ∀ (left₁ right₁ : Fin n → ℕ) (child₁ : ℕ),
      (((view n g).deg p = 1 ∧ child₁ = 0 ∧ left₁ = (view n g).left ∧
          right₁ = (view n g).right) ∨
        (2 ≤ (view n g).deg p ∧ ∃ r l : Fin n, (view n g).right cur = r.val ∧
          (view n g).left cur = l.val ∧ child₁ = r.val + 1 ∧
          left₁ = Function.update (view n g).left r l.val ∧
          right₁ = Function.update (view n g).right l r.val)) →
      view n g' = { view n g with
        deg := Function.update (view n g).deg p ((view n g).deg p - 1)
        child := Function.update (view n g).child p child₁
        left := left₁
        right := right₁ } → Q () g' t) :
    Record.wp (Cell.ok n) w (unlink cur p) Q g := by
  have hpn := p.isLt
  have hdp : g (.deg p) = (view n g).deg p := rfl
  by_cases h1 : (view n g).deg p - 1 = 0
  · simp only [unlink, Record.wp_bind, Record.wp_read, Record.wp_write, hdp, h1, ite_true,
      Cell.ok]
    refine ⟨hpn, ⟨hpn, fits_zero w⟩, ⟨hpn, fits_zero w⟩, hQ _ _ (by omega) _ _ 0
      (Or.inl ⟨by omega, rfl, rfl, rfl⟩) ?_⟩
    simp only [view_update_deg, view_update_child, h1]
  · obtain ⟨h, tail, -, hcirc, hcur, hlen, hpar⟩ := hdp2 (by omega)
    obtain ⟨r, l, -, hr, hl, -⟩ := hcirc.remove hcur hlen
    have hr' : g (.right cur) = r.val := hr
    have hl' : g (.left cur) = l.val := hl
    simp only [unlink, Record.wp_bind, Record.wp_read, Record.wp_write, hdp, h1, ite_false,
      Function.update_apply, reduceCtorEq, hr', hl', Cell.ok]
    refine ⟨hpn, ⟨hpn, hfit.of_le (by omega)⟩, cur.isLt, cur.isLt, ⟨r.isLt, hfit.of_le l.isLt.le⟩,
      ⟨l.isLt, hfit.of_le r.isLt.le⟩, ⟨hpn, hfit.of_le r.isLt⟩, hQ _ _ (by omega) _ _ _
      (Or.inr ⟨by omega, r, l, hr, hl, rfl, rfl, rfl⟩) ?_⟩
    simp only [view_update_deg, view_update_child, view_update_left, view_update_right]

/-- Moving the unlinked `cur` to the root list after the minimum root `m`, whose right neighbour
is `r'`, makes thirteen operations. -/
theorem wp_toRoot {g : Cell → ℕ} {cur m r' : Fin n} (hm : (view n g).minRoot = m.val + 1)
    (hr' : (view n g).right m = r'.val) (hfit : Fits w n) (hnr : (view n g).numRoots + 1 ≤ n)
    (hnm : (view n g).numMarked ≤ n) {Q : Unit → (Cell → ℕ) → ℕ → Prop}
    (hQ : ∀ g', view n g' = { view n g with
        left := Function.update (Function.update (view n g).left cur m.val) r' cur.val
        right := Function.update (Function.update (view n g).right cur r'.val) m cur.val
        par := Function.update (view n g).par cur 0
        mark := Function.update (view n g).mark cur 0
        numMarked := (view n g).numMarked - (view n g).mark cur
        numRoots := (view n g).numRoots + 1 } → Q () g' 13) :
    Record.wp (Cell.ok n) w (toRoot cur) Q g := by
  have hm' : g .minRoot = m.val + 1 := hm
  simp only [toRoot, Record.wp_read_bind, hm', Nat.add_sub_cancel]
  refine ⟨trivial, ?_⟩
  rw [Record.wp_bind]
  refine wp_spliceAfter hr' hfit ?_
  simp only [Record.wp_write_bind, Record.wp_read_bind, Record.wp_write, Function.update_apply,
    reduceCtorEq, ite_false, Cell.ok, true_and]
  refine ⟨⟨cur.isLt, fits_zero w⟩, cur.isLt, ⟨cur.isLt, fits_zero w⟩,
    hfit.of_le ((Nat.sub_le _ _).trans hnm), hfit.of_le hnr, hQ _ ?_⟩
  simp only [view_update_left, view_update_right, view_update_par, view_update_mark,
    view_update_numMarked, view_update_numRoots]
  rfl

/-- **One cut.** Cutting `cur` from its parent `p` evaluates to `CutsNode` in at most `20`
operations. The hypotheses are those of the hand-stepped `cutNodeCode_raw`. -/
theorem wp_cut {g : Cell → ℕ} {cur p m : Fin n} {rtail : List (Fin n)}
    (hdp_pos : 1 ≤ (view n g).deg p)
    (hdp2 : 2 ≤ (view n g).deg p → ∃ (h : Fin n) (tail : List (Fin n)),
      (view n g).child p = h.val + 1 ∧ IsCircList (view n g).left (view n g).right (h :: tail) ∧
      cur ∈ h :: tail ∧ 2 ≤ (h :: tail).length ∧ ∀ u ∈ h :: tail, (view n g).par u = p.val + 1)
    (hdp_le : (view n g).deg p ≤ n)
    (hmin : (view n g).minRoot = m.val + 1)
    (hcirc_r : IsCircList (view n g).left (view n g).right (m :: rtail))
    (hroots_par0 : ∀ u ∈ m :: rtail, (view n g).par u = 0)
    (hpar_cur : (view n g).par cur = p.val + 1)
    (hfit : Fits w n) (hnr : (view n g).numRoots + 1 ≤ n) (hnm : (view n g).numMarked ≤ n)
    {Q : Unit → (Cell → ℕ) → ℕ → Prop}
    (hQ : ∀ g' t, t ≤ 20 → CutsNode (view n g) cur p m rtail (view n g') → Q () g' t) :
    Record.wp (Cell.ok n) w (cut cur p) Q g := by
  rw [cut, Record.wp_bind]
  refine wp_unlink hdp_pos hdp2 hdp_le hfit fun g₁ t₁ ht₁ left₁ right₁ child₁ hunlink hg₁ => ?_
  -- The minimum root's right neighbour, after unlinking.
  have hr₁ : ∃ r' : Fin n, right₁ m = r'.val := by
    obtain ⟨r', hr', -⟩ := hcirc_r.right_head
    rcases hunlink with ⟨-, -, -, rfl⟩ | ⟨h2, r, l, -, hl, -, -, rfl⟩
    · exact ⟨r', hr'⟩
    · obtain ⟨h, tail, -, hcirc, hcur, hlen, hpar⟩ := hdp2 h2
      obtain ⟨r₂, l₂, -, -, hl₂, -, hl₂m, -⟩ := hcirc.remove hcur hlen
      obtain rfl : l₂ = l := Fin.ext (hl₂.symm.trans hl)
      have hml : m ≠ l₂ := fun e => by
        have := hroots_par0 m List.mem_cons_self
        rw [e, hpar l₂ hl₂m] at this
        omega
      exact ⟨r', by rw [Function.update_of_ne hml]; exact hr'⟩
  obtain ⟨r', hr'⟩ := hr₁
  refine wp_toRoot (by rw [hg₁]; exact hmin) (by rw [hg₁]; exact hr') hfit
    (by rw [hg₁]; exact hnr) (by rw [hg₁]; exact hnm) fun g₂ hg₂ => hQ _ _ (by omega) ?_
  rw [hg₂, hg₁]
  exact cutsNode_cutState hdp_pos hdp2 hcirc_r hroots_par0 hpar_cur hunlink hr'

/-- **Cascading cuts.** From a forest with `z` pending, the cascade leaves a forest with nothing
pending. Each cut costs at most `22` operations and releases one credit (one more root, one mark
less), so the whole cascade costs at most `53` operations plus the potential it releases. -/
theorem wp_cascade {K : ℕ} {s : IndexedMinPQ.State n} {v m : Fin n} (hfit : Fits w n) :
    ∀ (fuel : ℕ) {g : Cell → ℕ} {z : Fin n} {ts : List (FHTree n)},
      Cascading n K s (view n g) v m (some z) ts → (∃ T ∈ ts, T.root = v) →
      (∀ T ∈ ts, z ∈ T.nodes → T.root ≠ v) → z ∈ forestNodes ts →
      (view n g).numMarked < fuel →
      Record.wp (Cell.ok n) w (cascade fuel z) (fun _ g' t => ∃ ts',
        Cascading n K s (view n g') v m none ts' ∧ (∃ T ∈ ts', T.root = v) ∧
          t + potential n g' ≤ 53 + potential n g) g
  | 0, _, _, _, _, _, _, _, hfuel => absurd hfuel (Nat.not_lt_zero _)
  | fuel + 1, g, z, ts, h, hv, hzv, hz, hfuel => by
    have hzn := z.isLt
    simp only [cascade, Record.wp_read_bind, Cell.ok]
    refine ⟨hzn, ?_⟩
    by_cases hpz : (view n g).par z = 0
    · have hpz' : g (.par z) = 0 := hpz
      simp only [hpz', ite_true, Record.wp_pure]
      exact ⟨ts, h.clear_root hz hpz, hv, by omega⟩
    obtain ⟨T, hT, hdesc⟩ := h.desc_of_par hz hpz
    obtain ⟨p, -, hpar⟩ := (h.valid T hT).1.par_of_mem_children z hdesc
    obtain ⟨-, -, -, hinz, hmz1, -⟩ := exists_parent_info (h.valid T hT).1 hdesc hpar
    have hpar' : g (.par z) = p.val + 1 := hpar
    simp only [hpar', Nat.add_one_ne_zero, ite_false, Record.wp_read_bind, Nat.add_sub_cancel,
      Cell.ok]
    refine ⟨hzn, ?_⟩
    by_cases hmz : (view n g).mark z = 0
    · have hmz' : g (.mark z) = 0 := hmz
      have hc' := h.mark hz hpz hmz
      have hcount : (view n g).numMarked + 1 ≤ n :=
        calc (view n g).numMarked + 1 = markedCount _ := hc'.numMarked
          _ ≤ n := markedCount_le_n _
      simp only [hmz', ite_true, Record.wp_write_bind, Record.wp_read_bind, Record.wp_write,
        Function.update_apply, reduceCtorEq, ite_false, Cell.ok, true_and]
      refine ⟨⟨hzn, hfit.of_le (by omega)⟩, hfit.of_le hcount, ts, ?_, hv, ?_⟩
      · simp only [view_update_mark, view_update_numMarked]
        exact hc'
      · have : (view n g).numMarked = g .numMarked := rfl
        simp only [potential, credit, view_update_mark, view_update_numMarked]
        omega
    · have hmz' : g (.mark z) ≠ 0 := hmz
      simp only [hmz', ite_false]
      rw [Record.wp_bind]
      obtain ⟨rtail, hcirc, hperm⟩ := h.roots
      obtain ⟨hdp, hdp2, hdp_le, hroots0, hnr, hnm⟩ := h.cut_pre hperm hz hpar
      refine wp_cut hdp hdp2 hdp_le h.minRoot hcirc hroots0 hpar hfit hnr hnm
        fun g₁ t₁ ht₁ hcut => ?_
      obtain ⟨ts₁, hc₁, hv₁, hpv₁, hp₁⟩ :=
        hcut.cascading h hperm (Or.inr rfl) (Or.inr hv) hzv hz hpar
      have hpos : 1 ≤ (view n g).numMarked := by
        rw [h.numMarked]
        exact Finset.card_pos.mpr ⟨z, by simp [markedSet, hinz, hmz]⟩
      have hnm₁ : (view n g₁).numMarked + 1 = (view n g).numMarked := by
        rw [hcut.numMarked]; omega
      refine Record.wp_mono (fun _ g' t ⟨ts', hc', hv', hcost⟩ => ⟨ts', hc', hv', ?_⟩)
        (wp_cascade hfit fuel hc₁ hv₁ hpv₁ hp₁ (by omega))
      simp only [potential, credit] at hcost ⊢
      rw [hcut.numRoots] at hcost
      omega

/-- **Storing the key.** With the forest ready (`v` a root, or `v` not preceding the minimum
root), storing the key and updating the minimum root restores `FibRawInv`. -/
theorem wp_setKey {K : ℕ} {s' : IndexedMinPQ.State n} {g : Cell → ℕ} {v m : Fin n} {k : ℕ}
    (hm : (view n g).minRoot = m.val + 1) (hk : Fits w k) (hfit : Fits w n)
    (hpost : CutInv n K s' { view n g with key := Function.update (view n g).key v k } v m none ∨
      (FibRawInv n K s' { view n g with key := Function.update (view n g).key v k } ∧
        ¬IndexedMinPQ.PrioLT (v, k) (m, Function.update (view n g).key v k m)))
    {Q : Unit → (Cell → ℕ) → ℕ → Prop}
    (hQ : ∀ g' t, t ≤ 4 → FibRawInv n K s' (view n g') →
      (view n g').numRoots = (view n g).numRoots →
      (view n g').numMarked = (view n g).numMarked → Q () g' t) :
    Record.wp (Cell.ok n) w (setKey v k) Q g := by
  have hm' : g .minRoot = m.val + 1 := hm
  have hkm : Function.update g (.key v) k (.key m) = Function.update (view n g).key v k m := by
    by_cases hmv : m = v
    · subst hmv; simp
    · simp [Function.update_of_ne hmv, Fin.val_ne_of_ne hmv, view]
  simp only [setKey, Record.wp_write_bind, Record.wp_read_bind, Function.update_apply,
    reduceCtorEq, ite_false, hm', Nat.add_sub_cancel, Cell.ok, true_and]
  rw [← Function.update_apply (f := g), hkm]
  refine ⟨⟨v.isLt, hk⟩, m.isLt, ?_⟩
  by_cases hlt : IndexedMinPQ.PrioLT (v, k) (m, Function.update (view n g).key v k m)
  · have hlt' : IndexedMinPQ.RawPrioLT (↑v, k) (↑m, Function.update (view n g).key v k m) := hlt
    simp only [hlt', ite_true, Record.wp_write, Cell.ok, true_and]
    refine ⟨hfit.of_le v.isLt, hQ _ _ (by omega) ?_ rfl rfl⟩
    rcases hpost with hcut | ⟨-, hnlt⟩
    · simp only [view_update_minRoot, view_update_key]
      exact CutInv.to_fibRawInv hcut ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        (Or.inl ⟨by simpa using hlt, rfl⟩)
    · exact (hnlt hlt).elim
  · have hlt' : ¬IndexedMinPQ.RawPrioLT (↑v, k) (↑m, Function.update (view n g).key v k m) := hlt
    simp only [hlt', ite_false, Record.wp_pure]
    refine hQ _ _ (by omega) ?_ rfl rfl
    rcases hpost with hcut | ⟨hinv, -⟩
    · simp only [view_update_key]
      exact CutInv.to_fibRawInv hcut ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        (Or.inr ⟨by simpa using hlt, hm⟩)
    · simpa only [view_update_key] using hinv

/-- **Decreasing a key.** `decreaseKey n v k` lowers the key of the present handle `v` to `k`,
preserves the invariant, and costs at most `104` operations amortized. -/
theorem wp_decreaseKey {K : ℕ} {g : Cell → ℕ} {v : Fin n} {k₀ k : ℕ} (hI : Inv n K g)
    (hsv : abs n g v = some k₀) (hk₀ : k ≤ k₀) (hK : k ≤ K) (hfit : Fits w n)
    (hKfit : Fits w K) :
    Record.wp (Cell.ok n) w (decreaseKey n v k) (fun _ g' t =>
      abs n g' = Function.update (abs n g) v (some k) ∧ Inv n K g' ∧
        t + potential n g' ≤ 104 + potential n g) g := by
  have hvn := v.isLt
  have hkfit : Fits w k := hKfit.of_le hK
  obtain ⟨m, ts, hc⟩ := cascading_of_fibRawInv (v := v) hI (by simp [hsv])
  have hv_fn : v ∈ forestNodes ts := (hc.dom v).mpr (by simp [hsv])
  obtain ⟨Tv, hTv, hvT⟩ := mem_forestNodes_iff.mp hv_fn
  -- Every case ends in `setKey` from a state with the same counters as its potential says.
  have hdone : ∀ g' t, FibRawInv n K (Function.update (abs n g) v (some k)) (view n g') →
      t + potential n g' ≤ 104 + potential n g →
      abs n g' = Function.update (abs n g) v (some k) ∧ Inv n K g' ∧
        t + potential n g' ≤ 104 + potential n g := fun g' t hinv hcost => by
    obtain ⟨hI', habs⟩ := inv_of_fibRawInv hinv
    exact ⟨habs, hI', hcost⟩
  simp only [decreaseKey, Record.wp_read_bind, Cell.ok]
  refine ⟨hvn, ?_⟩
  by_cases hpv : (view n g).par v = 0
  · have hpv' : g (.par v) = 0 := hpv
    have hvr : v = Tv.root := ((hc.valid Tv hTv).par_eq_zero_iff_root hvT).mp hpv
    simp only [hpv', ne_eq, not_true_eq_false, ite_false]
    refine wp_setKey hc.minRoot hkfit hfit
      (Or.inl (hc.lowerRootKey ⟨Tv, hTv, hvr.symm⟩ hsv hk₀ hK)) fun g' t ht hinv hnr hnm => ?_
    have hpot : potential n g' = potential n g := by simp only [potential, hnr, hnm]
    exact hdone g' (t + 1) hinv (by omega)
  · obtain ⟨T, hT, hdesc⟩ := hc.desc_of_par hv_fn hpv
    obtain ⟨p, -, hpar⟩ := (hc.valid T hT).1.par_of_mem_children v hdesc
    have hpar' : g (.par v) = p.val + 1 := hpar
    simp only [hpar', ne_eq, Nat.add_one_ne_zero, not_false_eq_true, ite_true, Nat.add_sub_cancel,
      Record.wp_read_bind, Cell.ok]
    refine ⟨p.isLt, ?_⟩
    by_cases hlt : IndexedMinPQ.PrioLT (v, k) (p, (view n g).key p)
    · -- `v` now precedes its parent: cut it, cascade, and store the key.
      have hlt' : IndexedMinPQ.RawPrioLT (↑v, k) (↑p, g (.key ↑p)) := hlt
      simp only [hlt', ite_true]
      rw [Record.wp_bind]
      obtain ⟨rtail, hcirc, hperm⟩ := hc.roots
      obtain ⟨hdp, hdp2, hdp_le, hroots0, hnr, hnm⟩ := hc.cut_pre hperm hv_fn hpar
      refine wp_cut hdp hdp2 hdp_le hc.minRoot hcirc hroots0 hpar hfit hnr hnm
        fun g₁ t₁ ht₁ hcut => ?_
      have hv_ne : ∀ T ∈ ts, v ∈ T.nodes → T.root ≠ v := fun T hT _ e =>
        hpv (e ▸ (hc.valid T hT).2.1)
      obtain ⟨ts₁, hc₁, hv₁, hpv₁, hp₁⟩ :=
        hcut.cascading hc hperm (Or.inl rfl) (Or.inl rfl) hv_ne hv_fn hpar
      rw [Record.wp_bind]
      refine Record.wp_mono ?_ (wp_cascade hfit (n + 1) hc₁ hv₁ hpv₁ hp₁
        (by rw [hcut.numMarked]; omega))
      rintro _ g₂ t₂ ⟨ts₂, hc₂, hv₂, hcost₂⟩
      refine wp_setKey hc₂.minRoot hkfit hfit (Or.inl (hc₂.lowerRootKey hv₂ hsv hk₀ hK))
        fun g' t ht hinv hnr' hnm' => hdone g' _ hinv ?_
      have hΦ₁ : potential n g₁ ≤ potential n g + 24 := by
        simp only [potential, credit, hcut.numRoots, hcut.numMarked]
        omega
      have hΦ' : potential n g' = potential n g₂ := by simp only [potential, hnr', hnm']
      omega
    · -- `v` keeps its heap order: only the key changes.
      have hlt' : ¬IndexedMinPQ.RawPrioLT (↑v, k) (↑p, g (.key ↑p)) := hlt
      simp only [hlt', ite_false]
      obtain ⟨hinv, hnot⟩ := FibRawInv.lowerKey_noCut hI hsv hk₀ hK hpar hlt
      refine wp_setKey hc.minRoot hkfit hfit (Or.inr ⟨hinv, hnot m hc.minRoot⟩)
        fun g' t ht hinv' hnr hnm => ?_
      have hpot : potential n g' = potential n g := by simp only [potential, hnr, hnm]
      exact hdone g' (t + 1 + 1) hinv' (by omega)

end Programs

end Cslib.DataStructure.PriorityQueue.FibonacciHeap
