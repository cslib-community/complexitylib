/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.DataStructure.PriorityQueue.FibonacciHeap.Basic
public import Complexity.Foundations.Data.List.Perm

/-!
# Forest mathematics of Fibonacci-heap consolidation

This file holds the forest reasoning behind `extractMin` (`ExtractMin.lean`) as statements about
`RawState n` alone: no program appears. Each phase of `extractMin` has a precondition and a
result, and the lemmas here carry a phase's precondition to the next step's, moving trees between
the root list, the list still to be scattered and the consolidation table
[Fredman and Tarjan][FredmanTarjan1987] [Cormen et al., Section 19.2][CLRS2009].

* Linking (`LinksAs`, `Linked`): making one valid root the newest child of another of equal
  degree yields a valid root (`LinksAs.linked`, through the existing `ValidRoot.link`).
* Placing one tree into the table (`Placing`): an empty slot takes it (`Placing.place`); a full
  slot is emptied and its tree linked with it (`Placing.collide`).
* Scattering a list of trees (`Scattering`): the head is made an unmarked root
  (`Scattering.unmark`) and placed (`Scattering.placing`), and the rest is scattered
  (`Scattering.step`).
* Both results are `Consolidated`: the table holds trees on exactly the nodes scattered, and
  nothing else changed (`Scattered`).
* Gathering the table into a root list (`Gathering`, `Gathered`): `Gathering.take` adds one slot's
  tree, `Gathering.done` ends with an empty table.
* `extractMin` as a whole (`Detached`): `FibRawInv.detach` splits a heap into the minimum root's
  children and the other trees, and `Detached.finish` reassembles `FibRawInv` from the three
  phases' results.

The table invariant is the existing `SlotInv`, with its lemmas `lookup`, `step_collision`,
`insert_empty` and `done_of_cleared`; root lists reuse `RootList.addRoot`. The module adapts the
forest and table reasoning of Renfei Zhou's native formalization (`WordRAM/FibonacciHeap`, its
`Consolidate.lean`) to the record level, as `ExtractMin.lean` does for his programs.

## Main definitions

* `LinksAs`, `Linked`: linking two roots.
* `Scattered`, `Consolidated`: what a scattering phase changes, and its result.
* `Placing`, `Scattering`, `Gathering`, `Gathered`: the phases of consolidation.
* `unmarkState`, `detachState`: the states after unmarking a root and detaching the minimum.
* `Detached`: a nonempty heap split at its minimum root.

## Main results

* `LinksAs.linked`: linking two valid roots of equal degree yields a valid root.
* `Placing.place`, `Placing.collide`, `Scattering.step`, `Scattering.unmark`, `Gathering.take`:
  one step of each loop.
* `FibRawInv.detach`, `Detached.finish`: `extractMin` preserves `FibRawInv`.

## References

* [M. L. Fredman and R. E. Tarjan, *Fibonacci Heaps and Their Uses in Improved Network Optimization
  Algorithms*][FredmanTarjan1987]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Section 19.2][CLRS2009]
-/

@[expose] public section

namespace Cslib.DataStructure.PriorityQueue.FibonacciHeap

open Cslib.DataStructure.PriorityQueue
open Cslib.DataStructure.PriorityQueue.WordRAM.FibonacciHeap

variable {n : ℕ}

/-! ## Facts about subtrees, chains and the table -/

/-- The degree of a valid subtree's root is its number of children. -/
theorem ValidSubtree.deg_root {st : RawState n} {pending : Option (Fin n)} {T : FHTree n}
    (hT : ValidSubtree st pending T) : st.deg T.root = T.children.length := by
  cases hT with
  | mk _ _ hdeg _ _ _ _ _ => exact hdeg

/-- The child pointer of a valid subtree's root heads the circular list of its children. -/
theorem ValidSubtree.child_root {st : RawState n} {pending : Option (Fin n)} {T : FHTree n}
    (hT : ValidSubtree st pending T) :
    (T.children = [] ∧ st.child T.root = 0) ∨
      ∃ (h : Fin n) (tail : List (Fin n)), st.child T.root = h.val + 1 ∧
        IsCircList st.left st.right (h :: tail) ∧
          (h :: tail).Perm (T.children.map FHTree.root) := by
  cases hT with
  | mk _ _ _ hchild _ _ _ _ => exact hchild

/-- A valid subtree's root with children has a head child `c`, whose right neighbour is a handle. -/
theorem ValidSubtree.exists_child {st : RawState n} {pending : Option (Fin n)} {T : FHTree n}
    (hT : ValidSubtree st pending T) (h0 : st.deg T.root ≠ 0) :
    ∃ c r : Fin n, st.child T.root = c.val + 1 ∧ st.right c = r.val := by
  rcases ValidSubtree.child_root hT with ⟨hnil, _⟩ | ⟨c, tail, hc, hcirc, -⟩
  · exact absurd ((ValidSubtree.deg_root hT).trans (by simp [hnil])) h0
  · obtain ⟨r, hr, -⟩ := hcirc.right_head
    exact ⟨c, r, hc, hr⟩

/-- The root of a valid subtree has mark at most one. -/
theorem ValidSubtree.mark_root_le {st : RawState n} {pending : Option (Fin n)} {T : FHTree n}
    (hT : ValidSubtree st pending T) : st.mark T.root ≤ 1 := by
  cases hT with
  | mk _ hmark _ _ _ _ _ _ => exact hmark

/-- Clearing the parent and mark of a valid subtree's root makes it a valid root tree. -/
theorem ValidSubtree.unmarkRoot {st : RawState n} {T : FHTree n}
    (hT : ValidSubtree st none T) (hnd : T.nodes.Nodup) (numMarked : ℕ) :
    ValidRoot { st with
      par := Function.update st.par T.root 0
      mark := Function.update st.mark T.root 0
      numMarked := numMarked } none T := by
  have hne : ∀ x ∈ forestNodes T.children, x ≠ T.root := fun x hx e => by
    rw [T.nodes_eq] at hnd
    exact (List.nodup_cons.mp hnd).1 (e ▸ hx)
  refine ⟨hT.frame_root_mark hnd (by simp) ⟨rfl, rfl, rfl, rfl⟩
    (fun x hx => by simp [hne x hx]) (fun x hx => by simp [hne x hx]), by simp, by simp⟩

/-- Unmarking one present handle lowers the number of marks by its mark. -/
theorem markedCount_unmark {st st' : RawState n} {x : Fin n} (hin : st.inHeap x ≠ 0)
    (hmk : st.mark x ≤ 1) (hx : st'.mark x = 0) (hinh : st'.inHeap = st.inHeap)
    (hother : ∀ y, y ≠ x → st'.mark y = st.mark y) :
    markedCount st' = markedCount st - st.mark x := by
  have hiff : ∀ y, y ≠ x → ((st'.inHeap y ≠ 0 ∧ st'.mark y ≠ 0) ↔
      (st.inHeap y ≠ 0 ∧ st.mark y ≠ 0)) := fun y hy => by rw [hinh, hother y hy]
  by_cases hm0 : st.mark x = 0
  · rw [hm0, Nat.sub_zero]
    refine markedCount_congr fun y => ?_
    by_cases hy : y = x
    · subst hy; simp [hx, hm0]
    · exact hiff y hy
  · have := markedCount_clear_one hin hm0 hx hiff
    omega

/-- The children of a valid subtree are valid subtrees. -/
theorem ValidSubtree.sub {st : RawState n} {pending : Option (Fin n)} {T : FHTree n}
    (hT : ValidSubtree st pending T) : ∀ c ∈ T.children, ValidSubtree st pending c := by
  cases hT with
  | mk _ _ _ _ _ _ _ hsub => exact hsub

/-- In a chain of `right` pointers, `right x` is the next element. -/
theorem RightChain.right_head {right : Fin n → ℕ} {x : Fin n} {xs : List (Fin n)}
    (h : RightChain right (x :: xs)) : ∀ y ∈ xs.head?, right x = y.val := by
  cases xs with
  | nil => simp
  | cons y _ => simpa using h.1

/-- The tail of a chain of `right` pointers is a chain. -/
theorem RightChain.tail {right : Fin n → ℕ} {x : Fin n} {xs : List (Fin n)}
    (h : RightChain right (x :: xs)) : RightChain right xs := by
  cases xs with
  | nil => trivial
  | cons _ _ => exact h.2

/-- The table holds at most one tree per degree up to `maxDeg`. -/
theorem SlotInv.length_le {sz maxDeg : ℕ} {st : RawState n} {slots : List (FHTree n)}
    (h : SlotInv n sz st slots maxDeg) : slots.length ≤ maxDeg + 1 := by
  have hsub : (slots.map FHTree.deg).toFinset ⊆ Finset.range (maxDeg + 1) := fun d hd => by
    obtain ⟨T, hT, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hd)
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (h.2.1 T hT).2)
  have := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup h.1, List.length_map, Finset.card_range] at this
  exact this

/-- The largest degree in the table is logarithmic in the number of nodes. -/
theorem SlotInv.maxDeg_le {sz maxDeg : ℕ} {st : RawState n} {slots : List (FHTree n)}
    (h : SlotInv n sz st slots maxDeg) : maxDeg ≤ 2 * Nat.log 2 sz + 1 :=
  h.2.2.2.2.1

/-- Every degree up to the table's largest is a table index. -/
theorem SlotInv.le_n {sz maxDeg : ℕ} {st : RawState n} {slots : List (FHTree n)}
    (h : SlotInv n sz st slots maxDeg) {d : ℕ} (hd : d ≤ maxDeg) : d ≤ n := by
  rcases h.2.2.2.2.2 with h | h <;> omega

/-- Splitting a forest at one tree. -/
theorem forestNodes_perm_middle (slots rest : List (FHTree n)) (T : FHTree n) :
    (forestNodes (slots ++ T :: rest)).Perm (forestNodes (T :: slots) ++ forestNodes rest) :=
  (forestNodes_perm List.perm_middle).trans
    (by simp only [forestNodes, forestNodes_append, List.append_assoc, List.Perm.refl])

/-! ## What a phase changes -/

/-- `st'` agrees with `st` except on the tree fields and marks of `nodes`, the table and the number
of marks; and the number of marks stays correct and does not grow. -/
structure Scattered (st st' : RawState n) (nodes : List (Fin n)) : Prop where
  key : st'.key = st.key
  inHeap : st'.inHeap = st.inHeap
  minRoot : st'.minRoot = st.minRoot
  numRoots : st'.numRoots = st.numRoots
  sz : st'.sz = st.sz
  out : ∀ y ∉ nodes, st'.par y = st.par y ∧ st'.left y = st.left y ∧ st'.right y = st.right y ∧
    st'.child y = st.child y ∧ st'.deg y = st.deg y ∧ st'.mark y = st.mark y
  numMarked : st.numMarked = markedCount st → st'.numMarked = markedCount st'
  numMarked_le : st'.numMarked ≤ st.numMarked

/-- Nothing changed. -/
protected theorem Scattered.rfl {st : RawState n} {A : List (Fin n)} : Scattered st st A :=
  ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, id, le_rfl⟩

/-- Changing only the table. -/
theorem Scattered.cons (st : RawState n) (cons : ℕ → ℕ) (A : List (Fin n)) :
    Scattered st { st with cons := cons } A :=
  ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, id, le_rfl⟩

/-- `Scattered` composes. -/
theorem Scattered.trans {st st' st'' : RawState n} {A : List (Fin n)}
    (h₁ : Scattered st st' A) (h₂ : Scattered st' st'' A) : Scattered st st'' A := by
  refine ⟨h₂.key.trans h₁.key, h₂.inHeap.trans h₁.inHeap, h₂.minRoot.trans h₁.minRoot,
    h₂.numRoots.trans h₁.numRoots, h₂.sz.trans h₁.sz, fun y hy => ?_,
    fun h => h₂.numMarked (h₁.numMarked h), h₂.numMarked_le.trans h₁.numMarked_le⟩
  obtain ⟨a₁, b₁, c₁, d₁, e₁, f₁⟩ := h₁.out y hy
  obtain ⟨a₂, b₂, c₂, d₂, e₂, f₂⟩ := h₂.out y hy
  exact ⟨a₂.trans a₁, b₂.trans b₁, c₂.trans c₁, d₂.trans d₁, e₂.trans e₁, f₂.trans f₁⟩

/-- `Scattered` grows with the set of changed nodes. -/
theorem Scattered.mono {st st' : RawState n} {A B : List (Fin n)}
    (h : Scattered st st' A) (hAB : ∀ y ∈ A, y ∈ B) : Scattered st st' B :=
  { h with out := fun y hy => h.out y fun hA => hy (hAB y hA) }

/-- A valid root tree outside the changed nodes stays valid. -/
theorem Scattered.validRoot {st st' : RawState n} {A : List (Fin n)}
    (h : Scattered st st' A) {T : FHTree n} (hT : ValidRoot st none T)
    (hA : ∀ y ∈ T.nodes, y ∉ A) : ValidRoot st' none T :=
  hT.frame_nodes fun y hy => by
    obtain ⟨a, b, c, d, e, f⟩ := h.out y (hA y hy)
    exact ⟨congrFun h.inHeap y, f, e, d, congrFun h.key y, a, b, c⟩

/-- A valid subtree outside the changed nodes stays valid. -/
theorem Scattered.validSubtree {st st' : RawState n} {A : List (Fin n)}
    (h : Scattered st st' A) {T : FHTree n} (hT : ValidSubtree st none T)
    (hA : ∀ y ∈ T.nodes, y ∉ A) : ValidSubtree st' none T :=
  hT.frame (fun y hy => by
      obtain ⟨-, -, -, d, e, f⟩ := h.out y (hA y hy)
      exact ⟨congrFun h.inHeap y, f, e, d, congrFun h.key y⟩)
    fun y hy => by
      obtain ⟨a, b, c, -, -, -⟩ := h.out y (hA y (T.nodes_eq ▸ List.mem_cons_of_mem _ hy))
      exact ⟨a, b, c, Iff.rfl⟩

/-- The result of consolidating the nodes `A` from `st`: the table of `st'` holds `slots'`, of
largest degree `md'`, on exactly the nodes `A`, and only the nodes of `A` changed. -/
structure Consolidated (sz : ℕ) (st st' : RawState n) (A : List (Fin n))
    (slots' : List (FHTree n)) (md' : ℕ) : Prop where
  table : SlotInv n sz st' slots' md'
  perm : (forestNodes slots').Perm A
  scattered : Scattered st st' A

/-- A step that changed only nodes of `A` can precede a consolidation of `A`. -/
theorem Consolidated.pre {sz md' : ℕ} {st st₁ st' : RawState n} {A B : List (Fin n)}
    {slots' : List (FHTree n)} (hs : Scattered st st₁ A) (hc : Consolidated sz st₁ st' B slots' md')
    (hB : B.Perm A) : Consolidated sz st st' A slots' md' :=
  ⟨hc.table, hc.perm.trans hB, hs.trans (hc.scattered.mono fun _ hy => hB.subset hy)⟩

/-- Once a forest `cs` is consolidated into `slots`, adding the trees `E` changes nothing. -/
theorem Consolidated.perm_append {sz md : ℕ} {st st' : RawState n} {cs slots : List (FHTree n)}
    (hc : Consolidated sz st st' (forestNodes ([] ++ cs)) slots md) (E : List (FHTree n)) :
    (forestNodes (slots ++ E)).Perm (forestNodes (cs ++ E)) := by
  rw [forestNodes_append, forestNodes_append]
  simpa using hc.perm.append_right (forestNodes E)

/-! ## Linking two roots -/

/-- The effect of making root `x` the newest child of root `u`: `x` gets parent `u` and joins
`u`'s child list (alone, or after the head child `c`), and `u`'s degree grows by one. -/
def LinksAs (st : RawState n) (u x : Fin n) (st' : RawState n) : Prop :=
  (st.deg u = 0 ∧ st' = { st with
    par := Function.update st.par x (u.val + 1)
    left := Function.update st.left x x.val
    right := Function.update st.right x x.val
    child := Function.update st.child u (x.val + 1)
    deg := Function.update st.deg u 1 }) ∨
  ∃ c r : Fin n, st.deg u ≠ 0 ∧ st.child u = c.val + 1 ∧ st.right c = r.val ∧ st' = { st with
    par := Function.update st.par x (u.val + 1)
    left := Function.update (Function.update st.left x c.val) r x.val
    right := Function.update (Function.update st.right x r.val) c x.val
    deg := Function.update st.deg u (st.deg u + 1) }

/-- **Linking keeps a valid root**: if `u` precedes `x` and their trees have equal degrees, making
`x` the newest child of `u` yields a valid root tree; nodes outside the two trees keep every
field. -/
theorem LinksAs.validRoot {st st' : RawState n} {T₁ T₂ : FHTree n}
    (h₁ : ValidRoot st none T₁) (h₂ : ValidRoot st none T₂) (hnd : (T₁.nodes ++ T₂.nodes).Nodup)
    (hdeg : T₁.deg = T₂.deg)
    (hlt : IndexedMinPQ.PrioLT (T₁.root, st.key T₁.root) (T₂.root, st.key T₂.root))
    (hlink : LinksAs st T₁.root T₂.root st') :
    ValidRoot st' none (.node T₁.root (T₁.children ++ [T₂])) ∧
      ∀ y ∉ T₁.nodes ++ T₂.nodes, st'.par y = st.par y ∧ st'.left y = st.left y ∧
        st'.right y = st.right y ∧ st'.child y = st.child y ∧ st'.deg y = st.deg y := by
  have hu₁ : T₁.root ∈ T₁.nodes ++ T₂.nodes := List.mem_append_left _ T₁.root_mem_nodes
  have hx₂ : T₂.root ∈ T₁.nodes ++ T₂.nodes := List.mem_append_right _ T₂.root_mem_nodes
  have hux : T₁.root ≠ T₂.root := fun e =>
    (List.nodup_append.mp hnd).2.2 _ T₁.root_mem_nodes _ T₂.root_mem_nodes e
  -- `u`'s children are strict descendants of `T₁`, hence not `u` and not `x`.
  have hch_ne : ∀ c ∈ T₁.children, c.root ≠ T₁.root ∧ c.root ≠ T₂.root := fun c hc => by
    have hdesc : c.root ∈ forestNodes T₁.children :=
      mem_forestNodes_iff.mpr ⟨c, hc, c.root_mem_nodes⟩
    have hnd₁ := (List.nodup_append.mp hnd).1
    rw [T₁.nodes_eq] at hnd₁
    refine ⟨fun e => (List.nodup_cons.mp hnd₁).1 (e ▸ hdesc), fun e =>
      (List.nodup_append.mp hnd).2.2 _ (T₁.nodes_eq ▸ List.mem_cons_of_mem _ hdesc) _
        T₂.root_mem_nodes e⟩
  rcases hlink with ⟨hd0, rfl⟩ | ⟨c, r, hd0, hchild_u, hcr, rfl⟩
  · have hch_nil : T₁.children = [] := by
      have := h₁.1
      cases this with
      | mk _ _ hdeg' _ _ _ _ _ => simp_all
    refine ⟨h₁.link h₂ hnd hdeg hlt (fun _ _ => ⟨rfl, rfl, rfl⟩)
      ⟨by simp [FHTree.deg, hch_nil], ?_⟩
      ⟨by simp [Function.update_of_ne hux, h₁.2.1], by simp, fun y _ hy => by simp [hy]⟩
      ⟨⟨T₂.root, [], by simp, IsCircList.singleton _ _ _, by simp [hch_nil]⟩,
        fun y _ hy => by simp [hy]⟩
      (fun y _ hy _ => by simp [hy]), fun y hy => ?_⟩
    · intro y _ hy; simp [hy]
    · have hyu : y ≠ T₁.root := fun e => hy (e ▸ hu₁)
      have hyx : y ≠ T₂.root := fun e => hy (e ▸ hx₂)
      simp [hyu, hyx]
  · -- `u`'s child list is `c :: tail`, and `x` is spliced in after `c`.
    have hcirc : ∃ tail, IsCircList st.left st.right (c :: tail) ∧
        (c :: tail).Perm (T₁.children.map FHTree.root) := by
      rcases ValidSubtree.child_root h₁.1 with ⟨hnil, _⟩ | ⟨h, tail, hch, hcirc, hperm⟩
      · exact absurd ((ValidSubtree.deg_root h₁.1).trans (by simp [hnil])) hd0
      · obtain rfl : h = c := Fin.ext (by omega)
        exact ⟨tail, hcirc, hperm⟩
    obtain ⟨tail, hcirc, hperm⟩ := hcirc
    have hch_mem : ∀ y ∈ c :: tail, ∃ c' ∈ T₁.children, y = c'.root := fun y hy => by
      obtain ⟨c', hc', rfl⟩ := List.mem_map.mp (hperm.subset hy)
      exact ⟨c', hc', rfl⟩
    obtain ⟨r', hr', hr'_mem⟩ := hcirc.right_head
    obtain rfl : r' = r := Fin.ext (hr'.symm.trans hcr)
    obtain ⟨Cc, hCc, hc_eq⟩ := hch_mem c List.mem_cons_self
    obtain ⟨Cr, hCr, hr_eq⟩ := hch_mem r' hr'_mem
    have hx_notin : T₂.root ∉ c :: tail := fun hm => by
      obtain ⟨c', hc', e⟩ := hch_mem _ hm
      exact (hch_ne c' hc').2 e.symm
    have hcx : c ≠ T₂.root := fun e => hx_notin (e ▸ List.mem_cons_self)
    have hrx : r' ≠ T₂.root := fun e => hx_notin (e ▸ hr'_mem)
    have hcu : c ≠ T₁.root := hc_eq ▸ (hch_ne Cc hCc).1
    have hru : r' ≠ T₁.root := hr_eq ▸ (hch_ne Cr hCr).1
    have hc_nodes : c ∈ T₁.nodes ++ T₂.nodes := List.mem_append_left _ (T₁.nodes_eq ▸
      List.mem_cons_of_mem _ (mem_forestNodes_iff.mpr ⟨Cc, hCc, hc_eq ▸ Cc.root_mem_nodes⟩))
    have hr_nodes : r' ∈ T₁.nodes ++ T₂.nodes := List.mem_append_left _ (T₁.nodes_eq ▸
      List.mem_cons_of_mem _ (mem_forestNodes_iff.mpr ⟨Cr, hCr, hr_eq ▸ Cr.root_mem_nodes⟩))
    refine ⟨h₁.link h₂ hnd hdeg hlt (fun _ _ => ⟨rfl, rfl, rfl⟩)
      ⟨by simp [FHTree.deg, ValidSubtree.deg_root h₁.1], fun y _ hy => by simp [hy]⟩
      ⟨by simp [Function.update_of_ne hux, h₁.2.1], by simp, fun y _ hy => by simp [hy]⟩
      ⟨⟨c, T₂.root :: tail, hchild_u, hcirc.insertAfter hx_notin hcr,
        ?_⟩, fun _ _ _ => rfl⟩ (fun y _ hy hch => ?_), fun y hy => ?_⟩
    · simp only [List.map_append, List.map_cons, List.map_nil]
      exact (List.Perm.swap _ _ _).trans ((List.Perm.cons _ hperm).trans
        (List.perm_append_singleton _ _).symm)
    · have hyc : y ≠ c := fun e => hch Cc hCc (e.trans hc_eq)
      have hyr : y ≠ r' := fun e => hch Cr hCr (e.trans hr_eq)
      simp [hy, hyc, hyr]
    · have hyu : y ≠ T₁.root := fun e => hy (e ▸ hu₁)
      have hyx : y ≠ T₂.root := fun e => hy (e ▸ hx₂)
      have hyc : y ≠ c := fun e => hy (e ▸ hc_nodes)
      have hyr : y ≠ r' := fun e => hy (e ▸ hr_nodes)
      simp [hyu, hyx, hyc, hyr]

/-- The result of linking the roots of `T₁` and `T₂` into the tree `T`. -/
structure Linked (st st' : RawState n) (T₁ T₂ T : FHTree n) : Prop where
  deg : T.deg = T₁.deg + 1
  perm : T.nodes.Perm (T₁.nodes ++ T₂.nodes)
  valid : ValidRoot st' none T
  scattered : Scattered st st' (T₁.nodes ++ T₂.nodes)
  cons : st'.cons = st.cons

/-- Linking two valid roots of equal degree, the one that precedes becoming the parent. -/
theorem LinksAs.linked {st st' : RawState n} {T₁ T₂ : FHTree n}
    (h₁ : ValidRoot st none T₁) (h₂ : ValidRoot st none T₂) (hnd : (T₁.nodes ++ T₂.nodes).Nodup)
    (hdeg : T₁.deg = T₂.deg)
    (hlt : IndexedMinPQ.PrioLT (T₁.root, st.key T₁.root) (T₂.root, st.key T₂.root))
    (hlink : LinksAs st T₁.root T₂.root st') :
    Linked st st' T₁ T₂ (.node T₁.root (T₁.children ++ [T₂])) := by
  obtain ⟨hv, hout⟩ := LinksAs.validRoot h₁ h₂ hnd hdeg hlt hlink
  obtain ⟨hk, hin, hm, hmin, hnr, hnm, hsz, hcons⟩ : st'.key = st.key ∧
      st'.inHeap = st.inHeap ∧ st'.mark = st.mark ∧ st'.minRoot = st.minRoot ∧
      st'.numRoots = st.numRoots ∧ st'.numMarked = st.numMarked ∧ st'.sz = st.sz ∧
      st'.cons = st.cons := by
    rcases hlink with ⟨-, rfl⟩ | ⟨-, -, -, -, -, rfl⟩ <;>
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine ⟨by simp [FHTree.deg], by rw [link_nodes_eq, FHTree.eta], hv,
    ⟨hk, hin, hmin, hnr, hsz, fun y hy => ?_, fun h => ?_, hnm.le⟩, hcons⟩
  · obtain ⟨a, b, c, d, e⟩ := hout y hy
    exact ⟨a, b, c, d, e, congrFun hm y⟩
  · rw [hnm, h]
    exact markedCount_congr fun u => by rw [hin, hm]

/-- Linking is symmetric in the two trees given. -/
theorem Linked.symm {st st' : RawState n} {T₁ T₂ T : FHTree n} (h : Linked st st' T₂ T₁ T)
    (hdeg : T₁.deg = T₂.deg) : Linked st st' T₁ T₂ T :=
  ⟨h.deg.trans (by rw [hdeg]), h.perm.trans List.perm_append_comm, h.valid,
    h.scattered.mono fun _ hy => List.perm_append_comm.subset hy, h.cons⟩

/-! ## Placing one tree into the table -/

/-- The precondition of placing the valid root tree `T` into a consolidation table holding
`slots`: `z` is a handle outside all of them, and `sz` bounds their number of nodes. -/
structure Placing (sz : ℕ) (z : Fin n) (st : RawState n) (T : FHTree n) (slots : List (FHTree n))
    (md : ℕ) : Prop where
  table : SlotInv n sz st slots md
  valid : ValidRoot st none T
  nodup : (z :: forestNodes (T :: slots)).Nodup
  size : (forestNodes (T :: slots)).length ≤ sz

section Placing

variable {sz md : ℕ} {z : Fin n} {st : RawState n} {T : FHTree n} {slots : List (FHTree n)}

/-- The tree being placed has logarithmic degree, with room for one more link. -/
theorem Placing.deg_bounds (h : Placing sz z st T slots md) :
    T.deg ≤ 2 * Nat.log 2 sz + 1 ∧ T.deg + 2 ≤ n := by
  refine deg_bounds_of_extra ?_ h.valid.1
    (h.nodup.sublist (List.Sublist.cons_cons z (List.sublist_append_left _ _)))
  have := h.size
  simp only [forestNodes, List.length_append] at this
  unfold FHTree.size
  omega

/-- The table holds fewer trees than there are handles. -/
theorem Placing.length_lt (h : Placing sz z st T slots md) : slots.length < n := by
  have h1 := h.nodup.length_le_card
  have h2 := forestNodes_length_ge slots
  have h3 := T.size_pos
  simp only [forestNodes, List.length_cons, List.length_append, Fintype.card_fin] at h1
  unfold FHTree.size at h3
  omega

/-- **An empty slot.** If no tree in the table has `T`'s degree, storing `T` there places it. -/
theorem Placing.place (h : Placing sz z st T slots md) (hnone : ∀ R ∈ slots, R.deg ≠ T.deg) :
    Consolidated sz st { st with cons := Function.update st.cons T.deg (T.root.val + 1) }
      (forestNodes (T :: slots)) (T :: slots) (max md T.deg) :=
  ⟨h.table.insert_empty h.deg_bounds.2 h.deg_bounds.1 rfl hnone h.valid, .refl _, .cons _ _ _⟩

/-- **A collision.** If the table's tree `slots[i]` has `T`'s degree, then after emptying its slot
the two trees can be linked; the linked tree is then placed into the rest of the table, and
placing it places `T`. -/
theorem Placing.collide (h : Placing sz z st T slots md) {i : ℕ} (hi : i < slots.length)
    (hdi : slots[i].deg = T.deg) (hno : ∀ R ∈ slots.eraseIdx i, R.deg ≠ T.deg)
    {st₁ : RawState n} (h₁ : st₁ = { st with cons := Function.update st.cons T.deg 0 }) :
    ValidRoot st₁ none T ∧ ValidRoot st₁ none slots[i] ∧ (T.nodes ++ slots[i].nodes).Nodup ∧
      ∀ {st₂ : RawState n} {T' : FHTree n}, Linked st₁ st₂ T slots[i] T' →
        Placing sz z st₂ T' (slots.eraseIdx i) md ∧
          ∀ {st' : RawState n} {slots' : List (FHTree n)} {md' : ℕ},
            Consolidated sz st₂ st' (forestNodes (T' :: slots.eraseIdx i)) slots' md' →
              Consolidated sz st st' (forestNodes (T :: slots)) slots' md' := by
  subst h₁
  have hval : ∀ R, ValidRoot st none R →
      ValidRoot { st with cons := Function.update st.cons T.deg 0 } none R := fun R hR =>
    hR.frame_nodes fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hP : (forestNodes (T :: slots)).Perm
      ((T.nodes ++ slots[i].nodes) ++ forestNodes (slots.eraseIdx i)) := by
    rw [List.append_assoc]
    exact (forestNodes_eraseIdx_perm slots i hi).symm.append_left T.nodes
  have hnd := (List.nodup_cons.mp ((hP.cons z).nodup_iff.mp h.nodup)).2
  refine ⟨hval T h.valid, hval _ (h.table.2.1 _ (List.getElem_mem hi)).1,
    (List.nodup_append.mp hnd).1, fun {st₂ T'} hl => ?_⟩
  have hs₁ := h.table.step_collision hi hdi (by have := h.deg_bounds.2; omega) hno rfl
    fun R hR => hval R (h.table.2.1 R (List.mem_of_mem_eraseIdx hR)).1
  have hP' : (forestNodes (T' :: slots.eraseIdx i)).Perm (forestNodes (T :: slots)) :=
    (hl.perm.append_right _).trans hP.symm
  refine ⟨⟨hs₁.frame hl.cons fun R hR => hl.scattered.validRoot (hs₁.2.1 R hR).1
      fun y hy hy' => List.disjoint_of_nodup_append hnd hy' (mem_forestNodes_iff.mpr ⟨R, hR, hy⟩),
    hl.valid, (hP'.cons z).nodup_iff.mpr h.nodup, hP'.length_eq ▸ h.size⟩, fun hc => ?_⟩
  exact hc.pre ((Scattered.cons _ _ _).trans
    (hl.scattered.mono fun _ hy => hP.symm.subset (List.mem_append_left _ hy))) hP'

end Placing

/-! ## Scattering a list of trees -/

/-- The precondition of scattering the trees `rest` into a table holding `slots`: the roots of
`rest` are linked by `right` in this order, and without `prep` they are already unmarked roots.
`z` is a handle outside all the trees, and `sz` bounds their number of nodes. -/
structure Scattering (sz : ℕ) (z : Fin n) (prep : Bool) (st : RawState n)
    (slots rest : List (FHTree n)) (md : ℕ) : Prop where
  table : SlotInv n sz st slots md
  valid : ∀ T ∈ rest, ValidSubtree st none T
  root : prep = false → ∀ T ∈ rest, st.par T.root = 0 ∧ st.mark T.root = 0
  chain : RightChain st.right (rest.map FHTree.root)
  nodup : (z :: forestNodes (slots ++ rest)).Nodup
  size : (forestNodes (slots ++ rest)).length ≤ sz
  inHeap : ∀ y ∈ forestNodes rest, st.inHeap y ≠ 0
  numMarked : st.numMarked = markedCount st

/-- The state after making `x` an unmarked root: its parent and mark are cleared, and the number
of marks drops by its mark. -/
def unmarkState (st : RawState n) (x : Fin n) : RawState n :=
  { st with
    par := Function.update st.par x 0
    mark := Function.update st.mark x 0
    numMarked := st.numMarked - st.mark x }

section Scattering

variable {sz md : ℕ} {z : Fin n} {prep : Bool} {st : RawState n} {T : FHTree n}
  {slots rest : List (FHTree n)}

/-- With nothing left to scatter, the table is the result. -/
theorem Scattering.done (h : Scattering sz z prep st slots [] md) :
    Consolidated sz st st (forestNodes (slots ++ [])) slots md :=
  ⟨h.table, by simp, .rfl⟩

/-- Without `prep`, the next tree is a valid root. -/
theorem Scattering.validRoot (h : Scattering sz z false st slots (T :: rest) md) :
    ValidRoot st none T :=
  ⟨h.valid T List.mem_cons_self, h.root rfl T List.mem_cons_self⟩

/-- Once the next tree is a valid root, it can be placed. -/
theorem Scattering.placing (h : Scattering sz z prep st slots (T :: rest) md)
    (hT : ValidRoot st none T) : Placing sz z st T slots md := by
  have hP := forestNodes_perm_middle slots rest T
  have hlen := h.size
  rw [hP.length_eq, List.length_append] at hlen
  exact ⟨h.table, hT, ((hP.cons z).nodup_iff.mp h.nodup).sublist
    (List.Sublist.cons_cons z (List.sublist_append_left _ _)), by omega⟩

/-- **Making the next tree an unmarked root**, as `prep` does: the precondition still holds, the
tree is a valid root, and only its root changed. -/
theorem Scattering.unmark (h : Scattering sz z true st slots (T :: rest) md) :
    Scattering sz z true (unmarkState st T.root) slots (T :: rest) md ∧
      ValidRoot (unmarkState st T.root) none T ∧
        Scattered st (unmarkState st T.root) (forestNodes (slots ++ T :: rest)) := by
  have hP := forestNodes_perm_middle slots rest T
  have hnd := (List.nodup_cons.mp ((hP.cons z).nodup_iff.mp h.nodup)).2
  have hx : T.root ∈ forestNodes (T :: slots) := List.mem_append_left _ T.root_mem_nodes
  have hne : ∀ y ∈ forestNodes slots ++ forestNodes rest, y ≠ T.root := by
    intro y hy e
    subst e
    rcases List.mem_append.mp hy with hy | hy
    · exact List.disjoint_of_nodup_append (List.nodup_append.mp hnd).1 T.root_mem_nodes hy
    · exact List.disjoint_of_nodup_append hnd hx hy
  have hT := h.valid T List.mem_cons_self
  have hnm : (unmarkState st T.root).numMarked = markedCount (unmarkState st T.root) := by
    rw [markedCount_unmark (st' := unmarkState st T.root)
      (h.inHeap _ (List.mem_append_left _ T.root_mem_nodes)) (ValidSubtree.mark_root_le hT)
      (by simp [unmarkState]) rfl fun y hy => by simp [unmarkState, hy], ← h.numMarked]
    rfl
  have hslot : ∀ y ∈ forestNodes slots, y ≠ T.root := fun y hy => hne y (List.mem_append_left _ hy)
  have hrest : ∀ R ∈ rest, ∀ y ∈ R.nodes, y ≠ T.root := fun R hR y hy =>
    hne y (List.mem_append_right _ (mem_forestNodes_iff.mpr ⟨R, hR, hy⟩))
  refine ⟨⟨h.table.frame rfl fun R hR => (h.table.2.1 R hR).1.frame_nodes fun y hy => ?_,
    fun R hR => ?_, fun h => absurd h (by decide), h.chain, h.nodup, h.size, h.inHeap, hnm⟩,
    ValidSubtree.unmarkRoot hT (List.nodup_append.mp (List.nodup_append.mp hnd).1).1 _,
    ⟨rfl, rfl, rfl, rfl, rfl, fun y hy => ?_, fun _ => hnm, Nat.sub_le _ _⟩⟩
  · simp [unmarkState, hslot y (mem_forestNodes_iff.mpr ⟨R, hR, hy⟩)]
  · rcases List.mem_cons.mp hR with rfl | hR
    · exact (ValidSubtree.unmarkRoot hT
        (List.nodup_append.mp (List.nodup_append.mp hnd).1).1 _).1
    · exact (h.valid R (List.mem_cons_of_mem _ hR)).frame
        (fun y hy => by simp [unmarkState, hrest R hR y hy])
        fun y hy => by simp [unmarkState, hrest R hR y (R.nodes_eq ▸ List.mem_cons_of_mem _ hy)]
  · have hy' : y ≠ T.root := fun e => hy (hP.symm.subset (List.mem_append_left _ (e ▸ hx)))
    simp [unmarkState, hy']

/-- **Scattering the next tree.** Once the next tree is placed, the precondition holds for the
rest, and scattering the rest scatters the whole list. -/
theorem Scattering.step {st₂ : RawState n} {slots₂ : List (FHTree n)} {md₂ : ℕ}
    (h : Scattering sz z prep st slots (T :: rest) md)
    (hc : Consolidated sz st st₂ (forestNodes (T :: slots)) slots₂ md₂) :
    Scattering sz z prep st₂ slots₂ rest md₂ ∧
      ∀ {st' : RawState n} {slots' : List (FHTree n)} {md' : ℕ},
        Consolidated sz st₂ st' (forestNodes (slots₂ ++ rest)) slots' md' →
          Consolidated sz st st' (forestNodes (slots ++ T :: rest)) slots' md' := by
  have hP := forestNodes_perm_middle slots rest T
  have hP₂ : (forestNodes (slots₂ ++ rest)).Perm (forestNodes (slots ++ T :: rest)) := by
    rw [forestNodes_append]
    exact (hc.perm.append_right _).trans hP.symm
  have hnd := (List.nodup_cons.mp ((hP.cons z).nodup_iff.mp h.nodup)).2
  have hdisj : ∀ R ∈ rest, ∀ y ∈ R.nodes, y ∉ forestNodes (T :: slots) := fun R hR y hy hy' =>
    List.disjoint_of_nodup_append hnd hy' (mem_forestNodes_iff.mpr ⟨R, hR, hy⟩)
  have hout : ∀ R ∈ rest, _ := fun R hR => hc.scattered.out _ (hdisj R hR _ R.root_mem_nodes)
  refine ⟨⟨hc.table, fun R hR => hc.scattered.validSubtree (h.valid R (List.mem_cons_of_mem _ hR))
    (hdisj R hR), fun hp R hR => ?_, (RightChain.tail h.chain).frame fun x hx => ?_,
    (hP₂.cons z).nodup_iff.mpr h.nodup, hP₂.length_eq ▸ h.size, fun y hy => ?_,
    hc.scattered.numMarked h.numMarked⟩, fun hc' => hc'.pre
      (hc.scattered.mono fun _ hy => hP.symm.subset (List.mem_append_left _ hy)) hP₂⟩
  · obtain ⟨a, -, -, -, -, f⟩ := hout R hR
    obtain ⟨hp0, hm0⟩ := h.root hp R (List.mem_cons_of_mem _ hR)
    exact ⟨a.trans hp0, f.trans hm0⟩
  · obtain ⟨R, hR, rfl⟩ := List.mem_map.mp hx
    exact (hout R hR).2.2.1
  · rw [hc.scattered.inHeap]
    exact h.inHeap y (List.mem_append_right _ hy)

end Scattering

/-! ## Gathering the table into a root list -/

/-- The precondition of gathering a table holding `slots` into the root list holding `gs`. -/
structure Gathering (sz : ℕ) (st : RawState n) (gs slots : List (FHTree n)) (md : ℕ) : Prop where
  table : SlotInv n sz st slots md
  valid : ∀ T ∈ gs, ValidRoot st none T
  roots : RootList st gs
  numRoots : st.numRoots = gs.length
  nodup : (forestNodes (gs ++ slots)).Nodup

/-- The result of gathering the nodes `A` from `st`: the root list of `st'` holds `gs'`, on exactly
the nodes `A`, the table is empty, and keys, presence flags and marks did not change. -/
structure Gathered (st st' : RawState n) (A : List (Fin n)) (gs' : List (FHTree n)) : Prop where
  valid : ∀ T ∈ gs', ValidRoot st' none T
  roots : RootList st' gs'
  numRoots : st'.numRoots = gs'.length
  perm : (forestNodes gs').Perm A
  cons : ∀ d ≤ n, st'.cons d = 0
  key : st'.key = st.key
  inHeap : st'.inHeap = st.inHeap
  mark : st'.mark = st.mark
  numMarked : st'.numMarked = st.numMarked
  sz : st'.sz = st.sz

/-- Adding a root keeps every other valid root tree valid: only roots change sibling pointers. -/
theorem AddsRoot.validRoot_other {st st' : RawState n} {u : Fin n}
    {ts : List (FHTree n)} (hadd : AddsRoot st u st') (hrl : RootList st ts)
    (hts : ∀ T ∈ ts, ValidRoot st none T) (hu : st.par u = 0) {R : FHTree n}
    (hR : ValidRoot st none R) : ValidRoot st' none R := by
  have hpar : ∀ y ∈ forestNodes R.children, st.par y ≠ 0 := fun y hy => by
    obtain ⟨q, -, hq⟩ := hR.1.par_of_mem_children y hy
    omega
  have hroot0 : ∀ m : Fin n, ∀ rtail, (m :: rtail).Perm (ts.map FHTree.root) →
      ∀ y ∈ m :: rtail, st.par y = 0 := fun m rtail hperm y hy => by
    obtain ⟨T, hT, rfl⟩ := List.mem_map.mp (hperm.subset hy)
    exact (hts T hT).2.1
  rcases hadd with ⟨-, rfl⟩ | ⟨m, r, hm, hr, rfl⟩
  · refine hR.frame_tree (fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩) fun y hy => ?_
    have hyu : y ≠ u := fun e => hpar y hy (e ▸ hu)
    simp [hyu]
  · obtain ⟨m', rtail, hm', hcirc, hperm, -⟩ := hrl.resolve_left fun ⟨_, h0⟩ => by omega
    obtain rfl : m' = m := Fin.ext (by omega)
    obtain ⟨r', hr', hr'_mem⟩ := hcirc.right_head
    obtain rfl : r' = r := Fin.ext (hr'.symm.trans hr)
    refine hR.frame_tree (fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩) fun y hy => ?_
    have hyu : y ≠ u := fun e => hpar y hy (e ▸ hu)
    have hym : y ≠ m' := fun e => hpar y hy (e ▸ hroot0 m' rtail hperm m' List.mem_cons_self)
    have hyr : y ≠ r' := fun e => hpar y hy (e ▸ hroot0 m' rtail hperm r' hr'_mem)
    simp [hyu, hym, hyr]

section Gathering

variable {sz md : ℕ} {st : RawState n} {gs slots : List (FHTree n)}

/-- **The end of the table.** Once no tree has degree at most `md`, the table is empty. -/
theorem Gathering.done (h : Gathering sz st gs slots md) (hge : ∀ T ∈ slots, md + 1 ≤ T.deg) :
    slots = [] ∧ Gathered st st (forestNodes gs) gs := by
  obtain ⟨rfl, hcons⟩ := h.table.done_of_cleared fun d hd T hT he => by
    have := hge T hT
    omega
  exact ⟨rfl, h.valid, h.roots, h.numRoots, .refl _, hcons, rfl, rfl, rfl, rfl, rfl⟩

/-- **Taking one slot's tree.** If the table's tree `slots[i]` has degree `d`, then after emptying
its slot the tree can be added to the root list, as `addRoot` needs; then the precondition holds
for the rest, and gathering the rest gathers the whole table. -/
theorem Gathering.take (h : Gathering sz st gs slots md) {i d : ℕ} (hi : i < slots.length)
    (hdi : slots[i].deg = d) (hd : d ≤ n) (hno : ∀ R ∈ slots.eraseIdx i, R.deg ≠ d)
    {st₁ : RawState n} (h₁ : st₁ = { st with cons := Function.update st.cons d 0 }) :
    (st₁.minRoot = 0 ∨ ∃ (m : Fin n) (rtail : List (Fin n)),
      st₁.minRoot = m.val + 1 ∧ IsCircList st₁.left st₁.right (m :: rtail)) ∧
      st₁.numRoots + 1 ≤ n ∧
      ∀ {st₂ : RawState n}, AddsRoot st₁ slots[i].root st₂ →
        Gathering sz st₂ (slots[i] :: gs) (slots.eraseIdx i) md ∧
          ∀ {st' : RawState n} {gs' : List (FHTree n)},
            Gathered st₂ st' (forestNodes (slots[i] :: gs ++ slots.eraseIdx i)) gs' →
              Gathered st st' (forestNodes (gs ++ slots)) gs' := by
  subst h₁
  have hval : ∀ R, ValidRoot st none R →
      ValidRoot { st with cons := Function.update st.cons d 0 } none R := fun R hR =>
    hR.frame_nodes fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hP : (forestNodes (slots[i] :: gs ++ slots.eraseIdx i)).Perm
      (forestNodes (gs ++ slots)) := by
    rw [forestNodes_append, forestNodes_append]
    change (slots[i].nodes ++ forestNodes gs ++ forestNodes (slots.eraseIdx i)).Perm _
    rw [List.append_assoc]
    exact (List.perm_append_comm_assoc _ _ _).trans
      ((forestNodes_eraseIdx_perm slots i hi).append_left _)
  have hnd := hP.nodup_iff.mpr h.nodup
  rw [forestNodes_append] at hnd
  have hnd_S := (List.nodup_append.mp hnd).1
  have hS₁ := hval _ (h.table.2.1 _ (List.getElem_mem hi)).1
  have hgs₁ : ∀ T ∈ gs, ValidRoot { st with cons := Function.update st.cons d 0 } none T :=
    fun T hT => hval T (h.valid T hT)
  have hs₁ := h.table.step_collision hi hdi hd hno rfl
    fun R hR => hval R (h.table.2.1 R (List.mem_of_mem_eraseIdx hR)).1
  refine ⟨?_, ?_, fun hadd => ?_⟩
  · rcases h.roots with ⟨_, h0⟩ | ⟨m, rtail, hm, hcirc, -⟩
    exacts [Or.inl h0, Or.inr ⟨m, rtail, hm, hcirc⟩]
  · have h1 := forestNodes_length_ge (slots[i] :: gs)
    have h2 : (forestNodes (slots[i] :: gs)).length ≤ n := by simpa using hnd_S.length_le_card
    simp only [List.length_cons] at h1
    change st.numRoots + 1 ≤ n
    have := h.numRoots
    omega
  obtain ⟨hall, hrl₂⟩ := RootList.addRoot hnd_S hS₁ hgs₁ h.roots hadd
  have hother := fun R (hR : R ∈ slots.eraseIdx i) =>
    hadd.validRoot_other h.roots hgs₁ hS₁.2.1 (hs₁.2.1 R hR).1
  obtain ⟨l₂, r₂, m₂, rfl⟩ := hadd.exists_eq
  refine ⟨⟨hs₁.frame rfl hother, hall, hrl₂, by simp [h.numRoots], hP.nodup_iff.mpr h.nodup⟩,
    fun hG => ⟨hG.valid, hG.roots, hG.numRoots, hG.perm.trans hP, hG.cons, hG.key, hG.inHeap,
      hG.mark, hG.numMarked, hG.sz⟩⟩

end Gathering

/-! ## Extracting the minimum -/

/-- The state after removing the minimum root `m` from the presence flags and the count. -/
def detachState (st : RawState n) (m : Fin n) : RawState n :=
  { st with inHeap := Function.update st.inHeap m 0, sz := st.sz - 1 }

/-- A nonempty heap as `extractMin` sees it: the minimum root `m` has children `cs`, listed in
the order of their sibling list, and the other trees are `E`, listed in root-list order from
`m`'s right neighbour. The other fields are the rest of `FibRawInv`. -/
structure Detached (n K : ℕ) (s : IndexedMinPQ.State n) (st : RawState n) (m : Fin n)
    (cs E : List (FHTree n)) : Prop where
  minRoot : st.minRoot = m.val + 1
  findMin : IndexedMinPQ.findMin s = some (m, st.key m)
  mark : st.mark m = 0
  deg : st.deg m = cs.length
  numRoots : st.numRoots = E.length + 1
  child : ∀ y ∈ (cs.map FHTree.root).head?, st.child m - 1 = y.val
  right : ∀ y ∈ (E.map FHTree.root).head?, st.right m = y.val
  chainChildren : RightChain st.right (cs.map FHTree.root)
  chainRoots : RightChain st.right (E.map FHTree.root)
  children : ∀ T ∈ cs, ValidSubtree st none T
  roots : ∀ T ∈ E, ValidRoot st none T
  nodup : (m :: forestNodes (cs ++ E)).Nodup
  dom : ∀ v, v ∈ m :: forestNodes (cs ++ E) ↔ (s v).isSome
  inHeap : ∀ v, (st.inHeap v ≠ 0 ↔ (s v).isSome) ∧ st.inHeap v ≤ 1
  keys : ∀ v k, s v = some k → st.key v = k ∧ k ≤ K
  sz : st.sz = (IndexedMinPQ.dom s).card
  numMarked : st.numMarked = markedCount st
  cons : ∀ d ≤ n, st.cons d = 0
  degBound : cs.length ≤ 2 * Nat.log 2 (IndexedMinPQ.dom s).card + 1

/-- **Splitting a heap at its minimum root.** -/
theorem FibRawInv.detach {K : ℕ} {s : IndexedMinPQ.State n} {st : RawState n}
    (h : FibRawInv n K s st) {m : Fin n} (hm : st.minRoot = m.val + 1) :
    ∃ cs E, Detached n K s st m cs E := by
  obtain ⟨hfind, -, -⟩ := FibRawInv.findMin_eq_some h hm
  obtain ⟨ts, hts, hnd, hdom, hin, hkeys, hsz, hnr, hnm, hcons, hrl⟩ := h
  obtain ⟨m', rtail, hm', hcirc, hperm, -⟩ := hrl.resolve_left fun ⟨_, h0⟩ => by omega
  obtain rfl : m = m' := Fin.ext (by omega)
  obtain ⟨T, hT, hTm⟩ := List.mem_map.mp (hperm.subset List.mem_cons_self)
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hT
  -- The other trees, in root-list order.
  obtain ⟨E, hE, hEmap⟩ : ∃ E : List (FHTree n), E.Perm (l₁ ++ l₂) ∧ E.map FHTree.root = rtail := by
    refine List.Perm.exists_perm_map_eq ((List.perm_cons m).mp (hperm.trans ?_))
    rw [← hTm]
    simp
  -- The children, in sibling-list order.
  obtain ⟨cs, hcs, hhead, hchain⟩ : ∃ cs : List (FHTree n), cs.Perm T.children ∧
      (∀ y ∈ (cs.map FHTree.root).head?, st.child m - 1 = y.val) ∧
        RightChain st.right (cs.map FHTree.root) := by
    rcases ValidSubtree.child_root (hts T hT).1 with ⟨hnil, -⟩ | ⟨c, tail, hc, hcircC, hpermC⟩
    · exact ⟨[], by simp [hnil], by simp, trivial⟩
    · obtain ⟨cs, hcs, hmap⟩ := hpermC.exists_perm_map_eq
      refine ⟨cs, hcs, ?_, hmap ▸ hcircC.rightChain⟩
      rw [hmap, ← hTm]
      simp [hc]
  have hts' : (l₁ ++ T :: l₂).Perm (T :: E) := List.perm_middle.trans (hE.symm.cons T)
  have hfs : (forestNodes (l₁ ++ T :: l₂)).Perm (m :: forestNodes (cs ++ E)) := by
    refine (forestNodes_perm hts').trans ?_
    change (T.nodes ++ forestNodes E).Perm _
    rw [T.nodes_eq, hTm, forestNodes_append]
    exact ((forestNodes_perm hcs).symm.append_right _).cons m
  have hmem : ∀ R, R ∈ E → R ∈ l₁ ++ T :: l₂ := fun R hR =>
    hts'.symm.subset (List.mem_cons_of_mem _ hR)
  have hcard : (IndexedMinPQ.dom s).card = (forestNodes (l₁ ++ T :: l₂)).length := by
    rw [← List.toFinset_card_of_nodup hnd]
    congr 1
    ext y
    simp [IndexedMinPQ.dom, hdom y]
  have hchain0 := hcirc.rightChain
  refine ⟨cs, E, hm, hTm ▸ hfind, hTm ▸ (hts T hT).2.2, ?_, ?_, hhead, ?_, hchain,
    hEmap ▸ RightChain.tail hchain0, fun c hc => ValidSubtree.sub (hts T hT).1 c (hcs.subset hc),
    fun R hR => hts R (hmem R hR), hfs.nodup_iff.mp hnd, fun v => (hfs.mem_iff.symm).trans (hdom v),
    hin, hkeys, hsz, hnm, hcons, ?_⟩
  · rw [← hTm, ValidSubtree.deg_root (hts T hT).1, hcs.length_eq]
  · rw [hnr, hts'.length_eq, List.length_cons]
  · rw [hEmap]
    exact RightChain.right_head hchain0
  · rw [hcs.length_eq]
    refine (ValidSubtree.deg_bounds (hts T hT).1 ?_).1
    rw [hcard, FHTree.size, forestNodes_append]
    simp only [forestNodes, List.length_append]
    omega

section Detached

variable {K : ℕ} {s : IndexedMinPQ.State n} {st : RawState n} {m : Fin n} {cs E : List (FHTree n)}

/-- Every other node differs from the minimum root. -/
theorem Detached.ne_min (hD : Detached n K s st m cs E) {y : Fin n}
    (hy : y ∈ forestNodes (cs ++ E)) : y ≠ m := fun e =>
  (List.nodup_cons.mp hD.nodup).1 (e ▸ hy)

/-- After detaching `m`, the children are ready to be scattered with `prep`. -/
theorem Detached.scatterChildren (hD : Detached n K s st m cs E) :
    Scattering (forestNodes (cs ++ E)).length m true (detachState st m) [] cs 0 := by
  have hcs : ∀ y ∈ forestNodes cs, y ∈ forestNodes (cs ++ E) := fun y hy => by
    rw [forestNodes_append]
    exact List.mem_append_left _ hy
  refine ⟨SlotInv.empty hD.cons, fun T hT => (hD.children T hT).frame (fun y hy => ⟨?_, rfl, rfl,
    rfl, rfl⟩) fun _ _ => ⟨rfl, rfl, rfl, Iff.rfl⟩, fun h => absurd h (by decide), hD.chainChildren,
    hD.nodup.sublist (List.Sublist.cons_cons _ ?_), by simp [forestNodes_append], fun y hy => ?_,
    hD.numMarked.trans (markedCount_congr fun y => ?_).symm⟩
  · simp [detachState, hD.ne_min (hcs y (mem_forestNodes_iff.mpr ⟨T, hT, hy⟩))]
  · rw [List.nil_append, forestNodes_append]
    exact List.sublist_append_left _ _
  · simp only [detachState, Function.update_of_ne (hD.ne_min (hcs y hy))]
    exact (hD.inHeap y).1.mpr ((hD.dom y).mp (List.mem_cons_of_mem _ (hcs y hy)))
  · by_cases hy : y = m
    · subst hy
      simp [detachState, hD.mark]
    · simp [detachState, hy]

/-- After the children are scattered, the other trees are ready to be scattered without `prep`. -/
theorem Detached.scatterRoots (hD : Detached n K s st m cs E) {st₂ : RawState n}
    {slots : List (FHTree n)} {md : ℕ}
    (hc : Consolidated (forestNodes (cs ++ E)).length (detachState st m) st₂
      (forestNodes ([] ++ cs)) slots md) :
    Scattering (forestNodes (cs ++ E)).length m false st₂ slots E md := by
  have hdisj : ∀ R ∈ E, ∀ y ∈ R.nodes, y ∉ forestNodes ([] ++ cs) := fun R hR y hy hy' => by
    rw [List.nil_append] at hy'
    have := (List.nodup_cons.mp hD.nodup).2
    rw [forestNodes_append] at this
    exact List.disjoint_of_nodup_append this hy' (mem_forestNodes_iff.mpr ⟨R, hR, hy⟩)
  have hE : ∀ y ∈ forestNodes E, y ∈ forestNodes (cs ++ E) := fun y hy => by
    rw [forestNodes_append]
    exact List.mem_append_right _ hy
  have hP := hc.perm_append E
  have hroots : ∀ R ∈ E, ValidRoot st₂ none R := fun R hR =>
    hc.scattered.validRoot ((hD.roots R hR).frame_nodes fun y hy =>
      ⟨by simp [detachState, hD.ne_min (hE y (mem_forestNodes_iff.mpr ⟨R, hR, hy⟩))],
        rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩) (hdisj R hR)
  refine ⟨hc.table, fun R hR => (hroots R hR).1, fun _ R hR => (hroots R hR).2,
    hD.chainRoots.frame fun x hx => ?_, (hP.cons m).nodup_iff.mpr hD.nodup, hP.length_eq.le,
    fun y hy => ?_, hc.scattered.numMarked hD.scatterChildren.numMarked⟩
  · obtain ⟨R, hR, rfl⟩ := List.mem_map.mp hx
    exact (hc.scattered.out _ (hdisj R hR _ R.root_mem_nodes)).2.2.1
  · rw [hc.scattered.inHeap]
    simp only [detachState, Function.update_of_ne (hD.ne_min (hE y hy))]
    exact (hD.inHeap y).1.mpr ((hD.dom y).mp (List.mem_cons_of_mem _ (hE y hy)))

/-- After both scatterings, with the root list emptied, the table is ready to be gathered. -/
theorem Detached.gathering (hD : Detached n K s st m cs E) {st₂ st₃ : RawState n}
    {slots₁ slots₂ : List (FHTree n)} {md₁ md₂ : ℕ}
    (hc₁ : Consolidated (forestNodes (cs ++ E)).length (detachState st m) st₂
      (forestNodes ([] ++ cs)) slots₁ md₁)
    (hc₂ : Consolidated (forestNodes (cs ++ E)).length st₂ st₃ (forestNodes (slots₁ ++ E)) slots₂
      md₂) :
    Gathering (forestNodes (cs ++ E)).length { st₃ with minRoot := 0, numRoots := 0 } [] slots₂
      md₂ := by
  refine ⟨hc₂.table.frame rfl fun R hR => (hc₂.table.2.1 R hR).1.frame_nodes fun _ _ =>
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, by simp, Or.inl ⟨rfl, rfl⟩, rfl, ?_⟩
  rw [List.nil_append]
  exact (hc₂.perm.trans (hc₁.perm_append E)).nodup_iff.mpr (List.nodup_cons.mp hD.nodup).2

/-- **Reassembling the heap.** After both scatterings and the gathering, `FibRawInv` holds of the
queue without `m`; the number of marks has not grown, and the table's largest degree is
logarithmic. -/
theorem Detached.finish (hD : Detached n K s st m cs E) {st₂ st₃ st' : RawState n}
    {slots₁ slots₂ gs' : List (FHTree n)} {md₁ md₂ : ℕ}
    (hc₁ : Consolidated (forestNodes (cs ++ E)).length (detachState st m) st₂
      (forestNodes ([] ++ cs)) slots₁ md₁)
    (hc₂ : Consolidated (forestNodes (cs ++ E)).length st₂ st₃ (forestNodes (slots₁ ++ E)) slots₂
      md₂)
    (hG : Gathered { st₃ with minRoot := 0, numRoots := 0 } st' (forestNodes ([] ++ slots₂)) gs') :
    FibRawInv n K (Function.update s m none) st' ∧ st'.numMarked ≤ st.numMarked ∧
      md₂ ≤ 2 * Nat.log 2 (IndexedMinPQ.dom s).card + 1 := by
  have hP : (forestNodes gs').Perm (forestNodes (cs ++ E)) := by
    refine hG.perm.trans ?_
    rw [List.nil_append]
    exact hc₂.perm.trans (hc₁.perm_append E)
  have hkey : st'.key = st.key := hG.key.trans (hc₂.scattered.key.trans hc₁.scattered.key)
  have hinh : st'.inHeap = Function.update st.inHeap m 0 :=
    hG.inHeap.trans (hc₂.scattered.inHeap.trans hc₁.scattered.inHeap)
  have hmin : m ∉ forestNodes (cs ++ E) := (List.nodup_cons.mp hD.nodup).1
  have hcard : (IndexedMinPQ.dom s).card = (forestNodes (cs ++ E)).length + 1 := by
    rw [← List.length_cons, ← List.toFinset_card_of_nodup hD.nodup]
    congr 1
    ext y
    simp only [List.mem_toFinset, hD.dom y, IndexedMinPQ.mem_dom_iff, Option.isSome_iff_exists]
  have hnm₃ := hc₂.scattered.numMarked (hc₁.scattered.numMarked hD.scatterChildren.numMarked)
  refine ⟨⟨gs', hG.valid, hP.nodup_iff.mpr (List.nodup_cons.mp hD.nodup).2, fun y => ?_,
    fun y => ?_, fun y k hy => ?_, ?_, hG.numRoots, ?_, hG.cons, hG.roots⟩, ?_, ?_⟩
  · rw [hP.mem_iff]
    by_cases hy : y = m
    · subst hy
      simp [hmin]
    · rw [Function.update_of_ne hy, ← hD.dom y, List.mem_cons]
      simp [hy]
  · rw [hinh]
    by_cases hy : y = m
    · subst hy
      simp
    · rw [Function.update_of_ne hy, Function.update_of_ne hy]
      exact hD.inHeap y
  · have hym : y ≠ m := by
      rintro rfl
      simp at hy
    rw [Function.update_of_ne hym] at hy
    rw [hkey]
    exact hD.keys y k hy
  · rw [hG.sz, IndexedMinPQ.dom_erase_update,
      Finset.card_erase_of_mem (IndexedMinPQ.findMin_mem_dom hD.findMin)]
    change st₃.sz = _
    rw [hc₂.scattered.sz, hc₁.scattered.sz]
    change st.sz - 1 = _
    rw [hD.sz]
  · rw [hG.numMarked]
    exact hnm₃.trans (markedCount_congr fun u => by rw [hG.inHeap, hG.mark]).symm
  · rw [hG.numMarked]
    exact hc₂.scattered.numMarked_le.trans hc₁.scattered.numMarked_le
  · exact (SlotInv.maxDeg_le hc₂.table).trans (by
      have : Nat.log 2 (forestNodes (cs ++ E)).length ≤ Nat.log 2 (IndexedMinPQ.dom s).card :=
        Nat.log_mono_right (by omega)
      omega)

end Detached

end Cslib.DataStructure.PriorityQueue.FibonacciHeap
