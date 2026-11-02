/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.DataStructure.PriorityQueue.FibonacciHeap.DecreaseKey

/-!
# Fibonacci-heap `extractMin` over a record of named cells

`extractMin n` removes the minimum root `z` and consolidates
[Fredman and Tarjan][FredmanTarjan1987] [Cormen et al., Section 19.2][CLRS2009]:

1. `scatterList … true` walks `z`'s children along their sibling list, makes each an unmarked
   root, and `scatter`s it into the degree table `cons`. Scattering links the tree with the
   table's tree of equal degree (`link`, `linkAs`) until it reaches an empty slot.
2. `scatterList … false` does the same for the other roots, walking the root list from `z`'s
   right neighbour.
3. `gather` scans the table up to the largest degree placed, moving each tree to a new root list
   with `addRoot`, and empties the table.

The largest degree placed is a program value, returned by `scatter` and threaded through the
loops, so the record layout is the same as for the other operations.

The proof splits as in `Basic.lean` and `DecreaseKey.lean`:

* program evaluation: `wp_linkAs`, `wp_link`, `wp_scatter`, `wp_scatterList`, `wp_gather` and
  `wp_extractMin`. Each loop lemma is an induction carrying the existing table invariant
  `SlotInv`;
* forest mathematics on `RawState n`: `LinksAs.validRoot` (linking, through the existing
  `ValidRoot.link`), `ValidSubtree.unmarkRoot`, `markedCount_unmark`, `AddsRoot.validRoot_other`
  and `SlotInv.length_le`. They reuse `SlotInv.empty`, `lookup`, `step_collision`,
  `insert_empty`, `done_of_cleared`, `deg_bounds_of_extra`, `ValidSubtree.deg_bounds`,
  `RightChain` and `RootList.addRoot` unchanged. `Frames` and `Scattered` describe what a phase
  leaves unchanged.

Each link costs `14` operations and removes a tree; each scattered root costs at most `9` more;
each table slot costs at most `13`. With `credit = 24` per root, the roots' credits pay for
their scattering, and the amortized cost is at most `92 * (log₂ m + 1)` on a queue of `m`
handles (`extractCharge`), by the Fibonacci degree bound.

## Main definitions

* `linkAs`, `link`, `scatter`, `scatterList`, `gather`, `extractMin`: record programs.
* `LinksAs`: the effect of linking on the raw view.
* `Frames`, `Scattered`: the fields a phase leaves unchanged.
* `extractCharge`: the amortized charge `92 * (Nat.log 2 m + 1)`.

## Main results

* `LinksAs.validRoot`: linking two valid roots of equal degree yields a valid root.
* `wp_scatter`, `wp_scatterList`, `wp_gather`: the three phases.
* `wp_extractMin`: `extractMin` implements `IndexedMinPQ.step` with amortized cost
  `extractCharge`.

## References

* [M. L. Fredman and R. E. Tarjan, *Fibonacci Heaps and Their Uses in Improved Network Optimization
  Algorithms*][FredmanTarjan1987]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Section 19.2][CLRS2009]
-/

@[expose] public section

namespace Cslib.DataStructure.PriorityQueue.FibonacciHeap

open Cslib.WordRAM Cslib.DataStructure Cslib.DataStructure.PriorityQueue
open Cslib.DataStructure.PriorityQueue.WordRAM.FibonacciHeap

/-! ## Linking two roots -/

/-- Make root `x` the newest child of root `u`. -/
def linkAs (u x : ℕ) : Prog Unit := do
  wr (.par x) (u + 1)
  let d ← rd (.deg u)
  if d = 0 then
    wr (.left x) x
    wr (.right x) x
    wr (.child u) (x + 1)
  else
    let c ← rd (.child u)
    spliceAfter (c - 1) x
  wr (.deg u) (d + 1)

/-- The effect of making root `x` the newest child of root `u`: `x` gets parent `u` and joins
`u`'s child list (alone, or after the head child `c`), and `u`'s degree grows by one. -/
def LinksAs {n : ℕ} (st : RawState n) (u x : Fin n) (st' : RawState n) : Prop :=
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

/-- The degree of a valid subtree's root is its number of children. -/
theorem ValidSubtree.deg_root {n : ℕ} {st : RawState n} {pending : Option (Fin n)}
    {T : FHTree n} (hT : ValidSubtree st pending T) : st.deg T.root = T.children.length := by
  cases hT with
  | mk _ _ hdeg _ _ _ _ _ => exact hdeg

/-- The child pointer of a valid subtree's root heads the circular list of its children. -/
theorem ValidSubtree.child_root {n : ℕ} {st : RawState n} {pending : Option (Fin n)}
    {T : FHTree n} (hT : ValidSubtree st pending T) :
    (T.children = [] ∧ st.child T.root = 0) ∨
      ∃ (h : Fin n) (tail : List (Fin n)), st.child T.root = h.val + 1 ∧
        IsCircList st.left st.right (h :: tail) ∧
          (h :: tail).Perm (T.children.map FHTree.root) := by
  cases hT with
  | mk _ _ _ hchild _ _ _ _ => exact hchild

/-- **Linking keeps a valid root**: if `u` precedes `x` and their trees have equal degrees, making
`x` the newest child of `u` yields a valid root tree; nodes outside the two trees keep every
field. -/
theorem LinksAs.validRoot {n : ℕ} {st st' : RawState n} {T₁ T₂ : FHTree n}
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

/-- Link the roots `a` and `b` of equal degree: the one that precedes becomes the parent of the
other. Returns the new root. -/
def link (a b : ℕ) : Prog ℕ := do
  let ka ← rd (.key a)
  let kb ← rd (.key b)
  if IndexedMinPQ.RawPrioLT (b, kb) (a, ka) then
    linkAs b a
    pure b
  else
    linkAs a b
    pure a

/-- `st'` agrees with `st` except on the tree fields of `nodes` and on the consolidation table. -/
structure Frames {n : ℕ} (st st' : RawState n) (nodes : List (Fin n)) : Prop where
  key : st'.key = st.key
  inHeap : st'.inHeap = st.inHeap
  mark : st'.mark = st.mark
  minRoot : st'.minRoot = st.minRoot
  numRoots : st'.numRoots = st.numRoots
  numMarked : st'.numMarked = st.numMarked
  sz : st'.sz = st.sz
  out : ∀ y ∉ nodes, st'.par y = st.par y ∧ st'.left y = st.left y ∧ st'.right y = st.right y ∧
    st'.child y = st.child y ∧ st'.deg y = st.deg y

/-- Frames compose. -/
theorem Frames.trans {n : ℕ} {st st' st'' : RawState n} {A : List (Fin n)}
    (h₁ : Frames st st' A) (h₂ : Frames st' st'' A) : Frames st st'' A := by
  refine ⟨h₂.key.trans h₁.key, h₂.inHeap.trans h₁.inHeap, h₂.mark.trans h₁.mark,
    h₂.minRoot.trans h₁.minRoot, h₂.numRoots.trans h₁.numRoots, h₂.numMarked.trans h₁.numMarked,
    h₂.sz.trans h₁.sz, fun y hy => ?_⟩
  obtain ⟨a₁, b₁, c₁, d₁, e₁⟩ := h₁.out y hy
  obtain ⟨a₂, b₂, c₂, d₂, e₂⟩ := h₂.out y hy
  exact ⟨a₂.trans a₁, b₂.trans b₁, c₂.trans c₁, d₂.trans d₁, e₂.trans e₁⟩

/-- Frames grow with the set of changed nodes. -/
theorem Frames.mono {n : ℕ} {st st' : RawState n} {A B : List (Fin n)} (h : Frames st st' A)
    (hAB : ∀ y ∈ A, y ∈ B) : Frames st st' B :=
  { h with out := fun y hy => h.out y fun hA => hy (hAB y hA) }

/-- A valid root tree outside the changed nodes stays valid. -/
theorem Frames.validRoot {n : ℕ} {st st' : RawState n} {A : List (Fin n)} (h : Frames st st' A)
    {T : FHTree n} (hT : ValidRoot st none T) (hA : ∀ y ∈ T.nodes, y ∉ A) : ValidRoot st' none T :=
  hT.frame_nodes fun y hy => by
    obtain ⟨a, b, c, d, e⟩ := h.out y (hA y hy)
    exact ⟨congrFun h.inHeap y, congrFun h.mark y, e, d, congrFun h.key y, a, b, c⟩

/-- Linking changes no key, presence flag, mark, scalar or table entry. -/
theorem LinksAs.frames {n : ℕ} {st st' : RawState n} {u x : Fin n} {A : List (Fin n)}
    (hl : LinksAs st u x st')
    (hout : ∀ y ∉ A, st'.par y = st.par y ∧ st'.left y = st.left y ∧ st'.right y = st.right y ∧
      st'.child y = st.child y ∧ st'.deg y = st.deg y) :
    Frames st st' A ∧ st'.cons = st.cons := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hout⟩, ?_⟩ <;>
  rcases hl with ⟨-, rfl⟩ | ⟨-, -, -, -, -, rfl⟩ <;> rfl

/-- Place root `u` in the consolidation table: while the slot of its degree holds a root, empty
the slot, link the two roots and continue with the new root. Returns the largest degree placed,
at least `md`. `fuel` bounds the number of links. -/
def scatter : ℕ → ℕ → ℕ → Prog ℕ
  | 0, _, md => pure md
  | fuel + 1, u, md => do
    let d ← rd (.deg u)
    let c ← rd (.cons d)
    if c = 0 then
      wr (.cons d) (u + 1)
      pure (max md d)
    else
      wr (.cons d) 0
      let u' ← link u (c - 1)
      scatter fuel u' md

/-- Changing only the table frames every tree field. -/
theorem frames_cons {n : ℕ} (st : RawState n) (cons : ℕ → ℕ) (A : List (Fin n)) :
    Frames st { st with cons := cons } A :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl⟩⟩

/-- Scatter the `k` roots of a list linked by `right` from `x`. With `prep`, each is first made an
unmarked root: these are the children of the extracted minimum. -/
def scatterList (fuel : ℕ) (prep : Bool) : ℕ → ℕ → ℕ → Prog ℕ
  | 0, _, md => pure md
  | k + 1, x, md => do
    let nxt ← rd (.right x)
    if prep then
      wr (.par x) 0
      let mk ← rd (.mark x)
      wr (.mark x) 0
      let c ← rd .numMarked
      wr .numMarked (c - mk)
    let md' ← scatter fuel x md
    scatterList fuel prep k nxt md'

/-- `st'` agrees with `st` except on the tree fields and marks of `nodes`, the table and the number
of marks. -/
structure Scattered {n : ℕ} (st st' : RawState n) (nodes : List (Fin n)) : Prop where
  key : st'.key = st.key
  inHeap : st'.inHeap = st.inHeap
  minRoot : st'.minRoot = st.minRoot
  numRoots : st'.numRoots = st.numRoots
  sz : st'.sz = st.sz
  out : ∀ y ∉ nodes, st'.par y = st.par y ∧ st'.left y = st.left y ∧ st'.right y = st.right y ∧
    st'.child y = st.child y ∧ st'.deg y = st.deg y ∧ st'.mark y = st.mark y

/-- `Scattered` composes. -/
theorem Scattered.trans {n : ℕ} {st st' st'' : RawState n} {A : List (Fin n)}
    (h₁ : Scattered st st' A) (h₂ : Scattered st' st'' A) : Scattered st st'' A := by
  refine ⟨h₂.key.trans h₁.key, h₂.inHeap.trans h₁.inHeap, h₂.minRoot.trans h₁.minRoot,
    h₂.numRoots.trans h₁.numRoots, h₂.sz.trans h₁.sz, fun y hy => ?_⟩
  obtain ⟨a₁, b₁, c₁, d₁, e₁, f₁⟩ := h₁.out y hy
  obtain ⟨a₂, b₂, c₂, d₂, e₂, f₂⟩ := h₂.out y hy
  exact ⟨a₂.trans a₁, b₂.trans b₁, c₂.trans c₁, d₂.trans d₁, e₂.trans e₁, f₂.trans f₁⟩

/-- `Scattered` grows with the set of changed nodes. -/
theorem Scattered.mono {n : ℕ} {st st' : RawState n} {A B : List (Fin n)}
    (h : Scattered st st' A) (hAB : ∀ y ∈ A, y ∈ B) : Scattered st st' B :=
  { h with out := fun y hy => h.out y fun hA => hy (hAB y hA) }

/-- A frame is `Scattered`. -/
theorem Frames.scattered {n : ℕ} {st st' : RawState n} {A : List (Fin n)}
    (h : Frames st st' A) : Scattered st st' A := by
  refine ⟨h.key, h.inHeap, h.minRoot, h.numRoots, h.sz, fun y hy => ?_⟩
  obtain ⟨a, b, c, d, e⟩ := h.out y hy
  exact ⟨a, b, c, d, e, congrFun h.mark y⟩

/-- A valid subtree outside the changed nodes stays valid. -/
theorem Frames.validSubtree {n : ℕ} {st st' : RawState n} {A : List (Fin n)}
    (h : Frames st st' A) {T : FHTree n} (hT : ValidSubtree st none T)
    (hA : ∀ y ∈ T.nodes, y ∉ A) : ValidSubtree st' none T :=
  hT.frame (fun y hy => by
      obtain ⟨-, -, -, d, e⟩ := h.out y (hA y hy)
      exact ⟨congrFun h.inHeap y, congrFun h.mark y, e, d, congrFun h.key y⟩)
    fun y hy => by
      obtain ⟨a, b, c, -, -⟩ := h.out y (hA y (T.nodes_eq ▸ List.mem_cons_of_mem _ hy))
      exact ⟨a, b, c, Iff.rfl⟩

/-- The root of a valid subtree has mark at most one. -/
theorem ValidSubtree.mark_root_le {n : ℕ} {st : RawState n} {pending : Option (Fin n)}
    {T : FHTree n} (hT : ValidSubtree st pending T) : st.mark T.root ≤ 1 := by
  cases hT with
  | mk _ hmark _ _ _ _ _ _ => exact hmark

/-- Clearing the parent and mark of a valid subtree's root makes it a valid root tree. -/
theorem ValidSubtree.unmarkRoot {n : ℕ} {st : RawState n} {T : FHTree n}
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
theorem markedCount_unmark {n : ℕ} {st st' : RawState n} {x : Fin n} (hin : st.inHeap x ≠ 0)
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

/-- Move the table's roots at degrees `d, d + 1, …` (`k` slots) to the root list. -/
def gather : ℕ → ℕ → Prog Unit
  | 0, _ => pure ()
  | k + 1, d => do
    let c ← rd (.cons d)
    if c = 0 then gather k (d + 1)
    else
      wr (.cons d) 0
      addRoot (c - 1)
      gather k (d + 1)

/-- Adding a root keeps every other valid root tree valid: only roots change sibling pointers. -/
theorem AddsRoot.validRoot_other {n : ℕ} {st st' : RawState n} {u : Fin n}
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

/-- A valid root tree outside the scattered nodes stays valid. -/
theorem Scattered.validRoot {n : ℕ} {st st' : RawState n} {A : List (Fin n)}
    (h : Scattered st st' A) {T : FHTree n} (hT : ValidRoot st none T)
    (hA : ∀ y ∈ T.nodes, y ∉ A) : ValidRoot st' none T :=
  hT.frame_nodes fun y hy => by
    obtain ⟨a, b, c, d, e, f⟩ := h.out y (hA y hy)
    exact ⟨congrFun h.inHeap y, f, e, d, congrFun h.key y, a, b, c⟩

/-- The children of a valid subtree are valid subtrees. -/
theorem ValidSubtree.sub {n : ℕ} {st : RawState n} {pending : Option (Fin n)} {T : FHTree n}
    (hT : ValidSubtree st pending T) : ∀ c ∈ T.children, ValidSubtree st pending c := by
  cases hT with
  | mk _ _ _ _ _ _ _ hsub => exact hsub

/-- The table holds at most one tree per degree up to `maxDeg`. -/
theorem SlotInv.length_le {n sz maxDeg : ℕ} {st : RawState n} {slots : List (FHTree n)}
    (h : SlotInv n sz st slots maxDeg) : slots.length ≤ maxDeg + 1 := by
  have hsub : (slots.map FHTree.deg).toFinset ⊆ Finset.range (maxDeg + 1) := fun d hd => by
    obtain ⟨T, hT, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hd)
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (h.2.1 T hT).2)
  have := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup h.1, List.length_map, Finset.card_range] at this
  exact this

/-- Remove and return the minimum of a heap on `n` handles: detach the minimum root `z`, scatter
its children and the other roots into the table, and gather the table into a new root list. -/
def extractMin (n : ℕ) : Prog (Option (Fin n × ℕ)) := do
  let m ← rd .minRoot
  if m = 0 then pure none
  else
    let kz ← rd (.key (m - 1))
    wr (.inHeap (m - 1)) 0
    let c ← rd .sz
    wr .sz (c - 1)
    let rz ← rd (.right (m - 1))
    let nr ← rd .numRoots
    let dz ← rd (.deg (m - 1))
    let cz ← rd (.child (m - 1))
    let md ← scatterList (n + 1) true dz (cz - 1) 0
    let md' ← scatterList (n + 1) false (nr - 1) rz md
    wr .minRoot 0
    wr .numRoots 0
    gather (md' + 1) 0
    pure (if h : m - 1 < n then some (⟨m - 1, h⟩, kz) else none)

/-- The amortized charge of `extractMin` on a queue with `m` handles. -/
def extractCharge (m : ℕ) : ℕ := 92 * (Nat.log 2 m + 1)

section Programs

variable {n w : ℕ}

/-- Making `x` the newest child of `u` evaluates to `LinksAs` in at most nine operations. -/
theorem wp_linkAs {g : Cell → ℕ} {u x : Fin n}
    (hch : (view n g).deg u ≠ 0 → ∃ c r : Fin n, (view n g).child u = c.val + 1 ∧
      (view n g).right c = r.val)
    (hdeg : (view n g).deg u + 1 ≤ n) (hfit : Fits w n) {Q : Unit → (Cell → ℕ) → ℕ → Prop}
    (hQ : ∀ g' t, t ≤ 9 → LinksAs (view n g) u x (view n g') → Q () g' t) :
    Record.wp (Cell.ok n) w (linkAs u x) Q g := by
  have hun := u.isLt
  have hxn := x.isLt
  have hd : g (.deg u) = (view n g).deg u := rfl
  by_cases h0 : (view n g).deg u = 0
  · simp only [linkAs, Record.wp_write_bind, Record.wp_read_bind, Record.wp_write,
      Function.update_apply, reduceCtorEq, ite_false, hd, h0, ite_true, Cell.ok]
    split_ands
    all_goals try first | omega | exact hfit.of_le (by omega)
    refine hQ _ _ (by omega) (Or.inl ⟨h0, ?_⟩)
    simp only [view_update_par, view_update_left, view_update_right, view_update_child,
      view_update_deg]
  · obtain ⟨c, r, hc, hr⟩ := hch h0
    have hc' : g (.child u) = c.val + 1 := hc
    simp only [linkAs, Record.wp_write_bind, Record.wp_read_bind,
      Function.update_apply, reduceCtorEq, ite_false, hd, h0, hc', Nat.add_sub_cancel, Cell.ok]
    refine ⟨⟨hxn, hfit.of_le (by omega)⟩, hun, hun, ?_⟩
    rw [Record.wp_bind]
    refine wp_spliceAfter (by simpa using hr) hfit ?_
    simp only [Record.wp_write, Cell.ok]
    split_ands
    all_goals try first | omega | exact hfit.of_le (by omega)
    refine hQ _ _ (by omega) (Or.inr ⟨c, r, h0, hc, hr, ?_⟩)
    simp only [view_update_par, view_update_left, view_update_right, view_update_deg]

/-- **Linking two roots** of equal degree evaluates, in at most eleven operations, to a valid root
tree of one more degree on the same nodes, framing everything else. -/
theorem wp_link {g : Cell → ℕ} {T₁ T₂ : FHTree n} (h₁ : ValidRoot (view n g) none T₁)
    (h₂ : ValidRoot (view n g) none T₂) (hnd : (T₁.nodes ++ T₂.nodes).Nodup)
    (hdeg : T₁.deg = T₂.deg) (hdn : T₁.deg + 2 ≤ n) (hfit : Fits w n)
    {Q : ℕ → (Cell → ℕ) → ℕ → Prop}
    (hQ : ∀ g' t (T : FHTree n), t ≤ 11 → T.deg = T₁.deg + 1 →
      T.nodes.Perm (T₁.nodes ++ T₂.nodes) → ValidRoot (view n g') none T →
      Frames (view n g) (view n g') (T₁.nodes ++ T₂.nodes) →
      (view n g').cons = (view n g).cons → Q T.root g' t) :
    Record.wp (Cell.ok n) w (link T₁.root T₂.root) Q g := by
  have hch : ∀ T : FHTree n, ValidRoot (view n g) none T → (view n g).deg T.root ≠ 0 →
      ∃ c r : Fin n, (view n g).child T.root = c.val + 1 ∧ (view n g).right c = r.val :=
    fun T hT h0 => by
      rcases ValidSubtree.child_root hT.1 with ⟨hnil, _⟩ | ⟨c, tail, hc, hcirc, -⟩
      · exact absurd ((ValidSubtree.deg_root hT.1).trans (by simp [hnil])) h0
      · obtain ⟨r, hr, -⟩ := hcirc.right_head
        exact ⟨c, r, hc, hr⟩
  have hd₁ := ValidSubtree.deg_root h₁.1
  have hd₂ := ValidSubtree.deg_root h₂.1
  have e₁ : T₁.deg = T₁.children.length := rfl
  have e₂ : T₂.deg = T₂.children.length := rfl
  have hux : T₁.root ≠ T₂.root := fun e =>
    (List.nodup_append.mp hnd).2.2 _ T₁.root_mem_nodes _ T₂.root_mem_nodes e
  have hnd' : (T₂.nodes ++ T₁.nodes).Nodup := List.perm_append_comm.nodup_iff.mp hnd
  have hsub : ∀ y ∈ T₂.nodes ++ T₁.nodes, y ∈ T₁.nodes ++ T₂.nodes := fun y hy =>
    List.perm_append_comm.mem_iff.mp hy
  simp only [link, Record.wp_read_bind, Cell.ok]
  refine ⟨T₁.root.isLt, T₂.root.isLt, ?_⟩
  by_cases hlt : IndexedMinPQ.PrioLT (T₂.root, (view n g).key T₂.root)
      (T₁.root, (view n g).key T₁.root)
  · have hlt' : IndexedMinPQ.RawPrioLT (↑T₂.root, g (.key ↑T₂.root))
        (↑T₁.root, g (.key ↑T₁.root)) := hlt
    simp only [hlt', ite_true]
    rw [Record.wp_bind]
    refine wp_linkAs (hch T₂ h₂) (by omega) hfit fun g' t ht hl => ?_
    obtain ⟨hv, hout⟩ := LinksAs.validRoot h₂ h₁ hnd' hdeg.symm hlt hl
    obtain ⟨hfr, hcons⟩ := LinksAs.frames hl hout
    exact hQ g' _ (.node T₂.root (T₂.children ++ [T₁])) (by omega)
      (by simp [FHTree.deg]; omega) (by rw [link_nodes_eq, FHTree.eta]; exact List.perm_append_comm)
      hv (hfr.mono hsub) hcons
  · have hlt' : ¬IndexedMinPQ.RawPrioLT (↑T₂.root, g (.key ↑T₂.root))
        (↑T₁.root, g (.key ↑T₁.root)) := hlt
    have hlt₁ := (IndexedMinPQ.prioLT_or_prioLT_of_ne hux ((view n g).key T₁.root)
      ((view n g).key T₂.root)).resolve_right hlt
    simp only [hlt', ite_false]
    rw [Record.wp_bind]
    refine wp_linkAs (hch T₁ h₁) (by omega) hfit fun g' t ht hl => ?_
    obtain ⟨hv, hout⟩ := LinksAs.validRoot h₁ h₂ hnd hdeg hlt₁ hl
    obtain ⟨hfr, hcons⟩ := LinksAs.frames hl hout
    exact hQ g' _ (.node T₁.root (T₁.children ++ [T₂])) (by omega)
      (by simp [FHTree.deg]) (by rw [link_nodes_eq, FHTree.eta]) hv hfr hcons

/-- **Scattering one root.** Placing a valid root tree in the table keeps the table valid, on the
same nodes, framing everything else. Each link costs `14` operations and removes a tree, so the
cost is at most `3` plus `14` per tree removed. -/
theorem wp_scatter {sz : ℕ} {z : Fin n} (hfit : Fits w n) :
    ∀ (fuel : ℕ) {g : Cell → ℕ} {T : FHTree n} {slots : List (FHTree n)} {md : ℕ},
      SlotInv n sz (view n g) slots md → ValidRoot (view n g) none T →
      (z :: forestNodes (T :: slots)).Nodup → (forestNodes (T :: slots)).length ≤ sz →
      slots.length < fuel →
      Record.wp (Cell.ok n) w (scatter fuel T.root md) (fun md' g' t => ∃ slots',
        SlotInv n sz (view n g') slots' md' ∧
        (forestNodes slots').Perm (forestNodes (T :: slots)) ∧
        Frames (view n g) (view n g') (forestNodes (T :: slots)) ∧
        t + 14 * slots'.length ≤ 3 + 14 * (slots.length + 1)) g
  | 0, _, _, _, _, _, _, _, _, hfuel => absurd hfuel (Nat.not_lt_zero _)
  | fuel + 1, g, T, slots, md, hs, hT, hnd, hsz, hfuel => by
    have hTnd : (z :: T.nodes).Nodup :=
      (List.cons_sublist_cons.mpr (List.sublist_append_left _ _)).nodup hnd
    have hTsz : T.size ≤ sz := by
      have : T.nodes.length ≤ (forestNodes (T :: slots)).length := by
        simp [forestNodes]
      unfold FHTree.size; omega
    obtain ⟨hdlog, hdn⟩ := deg_bounds_of_extra hTsz hT.1 hTnd
    have hdeg : g (.deg T.root) = T.deg := ValidSubtree.deg_root hT.1
    simp only [scatter, Record.wp_read_bind, hdeg, Cell.ok]
    refine ⟨T.root.isLt, by omega, ?_⟩
    rcases hs.lookup (d := T.deg) (by omega) with ⟨h0, hnone⟩ | ⟨i, hi, hdi, hci, -, hno⟩
    · have h0' : g (.cons T.deg) = 0 := h0
      simp only [h0', ite_true, Record.wp_write_bind, Record.wp_pure, Cell.ok]
      refine ⟨⟨by omega, hfit.of_le T.root.isLt⟩, T :: slots,
        by simpa using hs.insert_empty hdn hdlog rfl hnone hT, List.Perm.refl _,
        by simpa using frames_cons (view n g) _ _, by simp⟩
    · set S := slots[i] with hS
      have hci' : g (.cons T.deg) = S.root.val + 1 := hci
      simp only [hci', Nat.add_one_ne_zero, ite_false, Record.wp_write_bind, Nat.add_sub_cancel,
        Cell.ok]
      refine ⟨⟨by omega, fits_zero w⟩, ?_⟩
      rw [Record.wp_bind]
      set g₁ := Function.update g (.cons T.deg) 0
      have hv₁ : view n g₁ = { view n g with cons := Function.update (view n g).cons T.deg 0 } :=
        view_update_cons g 0 T.deg
      have hval₁ : ∀ R, ValidRoot (view n g) none R → ValidRoot (view n g₁) none R := fun R hR =>
        hv₁ ▸ hR.frame_nodes fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      have hS_mem : S ∈ slots := List.getElem_mem hi
      have hs₁ := hs.step_collision hi hdi (by omega) hno (by rw [hv₁])
        fun R hR => hval₁ R (hs.2.1 R (List.mem_of_mem_eraseIdx hR)).1
      have hperm_slots := forestNodes_eraseIdx_perm slots i hi
      have hnd1 : (T.nodes ++ (S.nodes ++ forestNodes (slots.eraseIdx i))).Nodup :=
        ((List.Perm.append_left T.nodes hperm_slots).nodup_iff).mpr (List.nodup_cons.mp hnd).2
      rw [← List.append_assoc] at hnd1
      have hnd_TS : (T.nodes ++ S.nodes).Nodup := (List.nodup_append.mp hnd1).1
      have hdisj : ∀ R ∈ slots.eraseIdx i, ∀ y ∈ R.nodes, y ∉ T.nodes ++ S.nodes :=
        fun R hR y hy hyTS => (List.nodup_append.mp hnd1).2.2 y hyTS y
          (mem_forestNodes_iff.mpr ⟨R, hR, hy⟩) rfl
      refine wp_link (hval₁ T hT) (hval₁ S (hs.2.1 S hS_mem).1) hnd_TS hdi.symm (by omega) hfit
        fun g₂ t₂ T' ht₂ hdeg' hperm' hT' hfr₂ hcons₂ => ?_
      have hpermTE : (forestNodes (T' :: slots.eraseIdx i)).Perm (forestNodes (T :: slots)) := by
        change (T'.nodes ++ forestNodes (slots.eraseIdx i)).Perm (T.nodes ++ forestNodes slots)
        refine (hperm'.append_right _).trans ?_
        rw [List.append_assoc]
        exact hperm_slots.append_left _
      have hs₂ : SlotInv n sz (view n g₂) (slots.eraseIdx i) md :=
        hs₁.frame hcons₂ fun R hR => hfr₂.validRoot (hs₁.2.1 R hR).1 (hdisj R hR)
      have hlen := List.length_eraseIdx_add_one hi
      refine Record.wp_mono ?_ (wp_scatter hfit fuel hs₂ hT'
        ((hpermTE.cons z).nodup_iff.mpr hnd) (hpermTE.length_eq ▸ hsz) (by omega))
      rintro md' g' t₃ ⟨slots', hs', hp', hfr', hc'⟩
      have hsub₁ : ∀ y ∈ T.nodes ++ S.nodes, y ∈ forestNodes (T :: slots) := fun y hy =>
        hpermTE.subset (List.mem_append_left _ (hperm'.symm.subset hy))
      refine ⟨slots', hs', hp'.trans hpermTE, ?_, by omega⟩
      exact ((hv₁ ▸ frames_cons (view n g) _ _).trans (hfr₂.mono hsub₁)).trans
        (hfr'.mono fun y hy => hpermTE.subset hy)

/-- **Scattering a list of roots.** Walking `k` roots linked by `right` (each first made an unmarked
root if `prep`) and scattering each into the table leaves a valid table on the same nodes. Apart
from links, each root costs `4` operations, or `9` with `prep`. -/
theorem wp_scatterList {sz : ℕ} {z : Fin n} (hfit : Fits w n) (prep : Bool) {fuel : ℕ}
    (hfuel : n < fuel) :
    ∀ (k : ℕ) {g : Cell → ℕ} {x : ℕ} {xs : List (Fin n)} {rest slots : List (FHTree n)} {md : ℕ},
      SlotInv n sz (view n g) slots md →
      (∀ T ∈ rest, ValidSubtree (view n g) none T ∧
        (prep = false → (view n g).par T.root = 0 ∧ (view n g).mark T.root = 0)) →
      xs.Perm (rest.map FHTree.root) → xs.length = k →
      RightChain (view n g).right xs → (∀ y ∈ xs.head?, x = y.val) →
      (z :: forestNodes (slots ++ rest)).Nodup → (forestNodes (slots ++ rest)).length ≤ sz →
      (∀ y ∈ forestNodes rest, (view n g).inHeap y ≠ 0) →
      (view n g).numMarked = markedCount (view n g) →
      Record.wp (Cell.ok n) w (scatterList fuel prep k x md) (fun md' g' t => ∃ slots',
        SlotInv n sz (view n g') slots' md' ∧
        (forestNodes slots').Perm (forestNodes (slots ++ rest)) ∧
        Scattered (view n g) (view n g') (forestNodes (slots ++ rest)) ∧
        (view n g').numMarked = markedCount (view n g') ∧
        (view n g').numMarked ≤ (view n g).numMarked ∧
        t + 14 * slots'.length ≤ (if prep then 9 else 4) * k + 14 * (slots.length + k)) g
  | 0, g, x, xs, rest, slots, md, hs, _, hperm, hlen, _, _, _, _, _, hnm => by
    obtain rfl : xs = [] := List.eq_nil_of_length_eq_zero hlen
    obtain rfl : rest = [] := List.eq_nil_of_length_eq_zero (by simpa using hperm.length_eq.symm)
    simp only [scatterList, Record.wp_pure, List.append_nil]
    exact ⟨slots, hs, List.Perm.refl _, ⟨rfl, rfl, rfl, rfl, rfl,
      fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩, hnm, le_rfl, by simp⟩
  | k + 1, g, x, xs, rest, slots, md, hs, hrest, hperm, hlen, hchain, hx, hnd, hsz, hin, hnm => by
    obtain ⟨x', xs', rfl⟩ : ∃ x' xs', xs = x' :: xs' := by
      cases xs with
      | nil => simp at hlen
      | cons x' xs' => exact ⟨x', xs', rfl⟩
    obtain rfl : x = x'.val := hx x' rfl
    obtain ⟨Tx, hTx, hTx_root⟩ := List.mem_map.mp (hperm.subset List.mem_cons_self)
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hTx
    set rest' := rest.eraseIdx i
    have hperm_rest : (rest[i] :: rest').Perm rest := List.getElem_cons_eraseIdx_perm hi
    have hxs' : xs'.Perm (rest'.map FHTree.root) := by
      have := hperm.trans (hperm_rest.map FHTree.root).symm
      rw [List.map_cons, hTx_root] at this
      exact (List.perm_cons x').mp this
    have hnodes : (forestNodes (slots ++ rest)).Perm
        (rest[i].nodes ++ forestNodes (slots ++ rest')) := by
      rw [forestNodes_append, forestNodes_append]
      refine (List.Perm.append_left _ (forestNodes_perm hperm_rest).symm).trans ?_
      change (forestNodes slots ++ (rest[i].nodes ++ forestNodes rest')).Perm
        (rest[i].nodes ++ (forestNodes slots ++ forestNodes rest'))
      rw [← List.append_assoc, ← List.append_assoc]
      exact List.perm_append_comm.append_right _
    have hTmem : rest[i] ∈ rest := List.getElem_mem hi
    have hnd' := (hnodes.cons z).nodup_iff.mp hnd
    have hTnd : rest[i].nodes.Nodup := (List.nodup_append.mp (List.nodup_cons.mp hnd').2).1
    have hdisj : ∀ y ∈ rest[i].nodes, y ∉ forestNodes (slots ++ rest') := fun y hy hy' =>
      (List.nodup_append.mp (List.nodup_cons.mp hnd').2).2.2 y hy y hy' rfl
    have hsub_rest : ∀ y ∈ forestNodes rest', y ∈ forestNodes (slots ++ rest') := fun y hy => by
      rw [forestNodes_append]; exact List.mem_append_right _ hy
    have hsub_slots : ∀ y ∈ forestNodes slots, y ∈ forestNodes (slots ++ rest') := fun y hy => by
      rw [forestNodes_append]; exact List.mem_append_left _ hy
    have hsubA : ∀ y ∈ forestNodes (slots ++ rest'), y ∈ forestNodes (slots ++ rest) :=
      fun y hy => hnodes.symm.subset (List.mem_append_right _ hy)
    have hsubT : ∀ y ∈ rest[i].nodes, y ∈ forestNodes (slots ++ rest) :=
      fun y hy => hnodes.symm.subset (List.mem_append_left _ hy)
    have hrest'_mem : ∀ T ∈ rest', T ∈ rest := fun T hT => List.mem_of_mem_eraseIdx hT
    have hx'_root : x' = rest[i].root := hTx_root.symm
    have hnext : ∀ y ∈ xs'.head?, (view n g).right x' = y.val := by
      intro y hy
      cases xs' with
      | nil => simp at hy
      | cons y' _ =>
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
        subst hy
        exact hchain.1
    have hchain' : RightChain (view n g).right xs' := by
      cases xs' with
      | nil => trivial
      | cons _ _ => exact hchain.2
    -- After the optional preparation, scatter `rest[i]` and continue.
    have cont : ∀ (g₁ : Cell → ℕ) (c₀ : ℕ), c₀ + 3 ≤ (if prep then 9 else 4) →
        ValidRoot (view n g₁) none rest[i] → SlotInv n sz (view n g₁) slots md →
        Scattered (view n g) (view n g₁) (forestNodes (slots ++ rest)) →
        (view n g₁).numMarked = markedCount (view n g₁) →
        (view n g₁).numMarked ≤ (view n g).numMarked →
        (∀ T ∈ rest', ValidSubtree (view n g₁) none T ∧
          (prep = false → (view n g₁).par T.root = 0 ∧ (view n g₁).mark T.root = 0)) →
        (view n g₁).right = (view n g).right →
        Record.wp (Cell.ok n) w (scatter fuel x' md >>= fun md' =>
          scatterList fuel prep k ((view n g).right x') md') (fun md' g' t => ∃ slots',
          SlotInv n sz (view n g') slots' md' ∧
          (forestNodes slots').Perm (forestNodes (slots ++ rest)) ∧
          Scattered (view n g) (view n g') (forestNodes (slots ++ rest)) ∧
          (view n g').numMarked = markedCount (view n g') ∧
          (view n g').numMarked ≤ (view n g).numMarked ∧
          t + c₀ + 14 * slots'.length ≤ (if prep then 9 else 4) * (k + 1) +
            14 * (slots.length + (k + 1))) g₁ := by
      intro g₁ c₀ hc₀ hT₁ hs₁ hsc₁ hnm₁ hle₁ hrest₁ hright₁
      rw [Record.wp_bind, hx'_root]
      have hnd_s : (z :: forestNodes (rest[i] :: slots)).Nodup := by
        refine List.Sublist.nodup ?_ hnd'
        refine List.Sublist.cons_cons z ?_
        change (rest[i].nodes ++ forestNodes slots).Sublist _
        rw [forestNodes_append]
        exact (List.sublist_append_left _ _).append_left _
      have hlen_s : (forestNodes (rest[i] :: slots)).length ≤ sz := by
        have h1 := hnodes.length_eq
        simp only [forestNodes_append, List.length_append] at h1 hsz
        change (rest[i].nodes ++ forestNodes slots).length ≤ sz
        simp only [List.length_append]
        omega
      have hslots_lt : slots.length < fuel := by
        have h1 : slots.length ≤ (forestNodes slots).length := forestNodes_length_ge slots
        have h2 : (forestNodes slots).length ≤ n := by
          have := (List.nodup_cons.mp hnd_s).2
          change (rest[i].nodes ++ forestNodes slots).Nodup at this
          simpa using (List.nodup_append.mp this).2.1.length_le_card
        omega
      refine wp_scatter (z := z) hfit fuel hs₁ hT₁ hnd_s hlen_s hslots_lt |> Record.wp_mono ?_
      rintro md₂ g₂ t₂ ⟨slots₂, hs₂, hp₂, hfr₂, hc₂⟩
      have hnd_sr : (forestNodes (slots ++ rest')).Nodup :=
        (List.nodup_append.mp (List.nodup_cons.mp hnd').2).2.1
      have hdisj2 : ∀ T ∈ rest', ∀ y ∈ T.nodes, y ∉ forestNodes (rest[i] :: slots) := by
        intro T hT y hy hy'
        have hyr : y ∈ forestNodes rest' := mem_forestNodes_iff.mpr ⟨T, hT, hy⟩
        change y ∈ rest[i].nodes ++ forestNodes slots at hy'
        rcases List.mem_append.mp hy' with h | h
        · exact hdisj y h (hsub_rest y hyr)
        · rw [forestNodes_append] at hnd_sr
          exact (List.nodup_append.mp hnd_sr).2.2 y h y hyr rfl
      have hP : (forestNodes (slots₂ ++ rest')).Perm (rest[i].nodes ++ forestNodes (slots ++ rest'))
          := by
        rw [forestNodes_append, forestNodes_append, ← List.append_assoc]
        exact hp₂.append_right _
      have hsub₂ : ∀ y ∈ forestNodes (rest[i] :: slots), y ∈ forestNodes (slots ++ rest) := by
        intro y hy
        change y ∈ rest[i].nodes ++ forestNodes slots at hy
        rcases List.mem_append.mp hy with h | h
        · exact hsubT y h
        · exact hsubA y (hsub_slots y h)
      have hrest₂ : ∀ T ∈ rest', ValidSubtree (view n g₂) none T ∧
          (prep = false → (view n g₂).par T.root = 0 ∧ (view n g₂).mark T.root = 0) :=
        fun T hT => ⟨hfr₂.validSubtree (hrest₁ T hT).1 (hdisj2 T hT), fun hp => by
          obtain ⟨hp0, hm0⟩ := (hrest₁ T hT).2 hp
          obtain ⟨a, -, -, -, -⟩ := hfr₂.out _ (hdisj2 T hT _ T.root_mem_nodes)
          exact ⟨a.trans hp0, (congrFun hfr₂.mark _).trans hm0⟩⟩
      have hchain₂ : RightChain (view n g₂).right xs' := hchain'.frame fun y hy => by
        obtain ⟨T, hT, rfl⟩ := List.mem_map.mp (hxs'.subset hy)
        obtain ⟨-, -, c, -, -⟩ := hfr₂.out _ (hdisj2 T hT _ T.root_mem_nodes)
        rw [c, hright₁]
      have hnext' : ∀ y ∈ xs'.head?, (view n g).right rest[i].root = y.val := hx'_root ▸ hnext
      refine wp_scatterList hfit prep hfuel k hs₂ hrest₂ hxs' (by simpa using hlen)
          hchain₂ hnext' ((hP.cons z).nodup_iff.mpr hnd')
          (by rw [hP.length_eq]; rw [hnodes.length_eq] at hsz; exact hsz)
          (fun y hy => by
            rw [hfr₂.inHeap, hsc₁.inHeap]
            exact hin y (mem_forestNodes_iff.mpr (by
              obtain ⟨T, hT, hyT⟩ := mem_forestNodes_iff.mp hy
              exact ⟨T, hrest'_mem T hT, hyT⟩)))
          (by
            rw [hfr₂.numMarked, hnm₁]
            exact markedCount_congr fun u => by rw [hfr₂.inHeap, hfr₂.mark]) |> Record.wp_mono ?_
      rintro md' g' t' ⟨slots', hs', hp', hsc', hnm', hle', hc'⟩
      refine ⟨slots', hs', hp'.trans (hP.trans hnodes.symm),
        (hsc₁.trans (hfr₂.scattered.mono hsub₂)).trans (hsc'.mono fun y hy =>
          hnodes.symm.subset (hP.subset hy)), hnm', ?_, ?_⟩
      · rw [hfr₂.numMarked] at hle'; omega
      · rw [Nat.mul_succ]; omega
    cases prep
    · simp only [scatterList, Record.wp_read_bind, Cell.ok, Bool.false_eq_true, ite_false]
      refine ⟨x'.isLt, Record.wp_mono (fun _ _ _ ⟨sl, a, b, c, d, e, f⟩ => ⟨sl, a, b, c, d, e,
        by simp only [Bool.false_eq_true, ite_false] at f; omega⟩)
        (cont g 1 (by simp) ?_ hs ⟨rfl, rfl, rfl, rfl, rfl,
          fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩ hnm le_rfl
          (fun T hT => hrest T (hrest'_mem T hT)) rfl)⟩
      obtain ⟨hv, h0⟩ := hrest _ hTmem
      exact ⟨hv, (h0 rfl).1, (h0 rfl).2⟩
    · simp only [scatterList, Record.wp_read_bind, Record.wp_write_bind, Cell.ok, ite_true,
        Function.update_apply, reduceCtorEq, ite_false]
      have hxn := x'.isLt
      have hmk := ValidSubtree.mark_root_le (hrest _ hTmem).1
      rw [← hx'_root] at hmk
      have hin_x : (view n g).inHeap x' ≠ 0 :=
        hin x' (mem_forestNodes_iff.mpr ⟨_, hTmem, hx'_root ▸ rest[i].root_mem_nodes⟩)
      have hnm_le : (view n g).numMarked ≤ n := hnm ▸ markedCount_le_n _
      set st₁ : RawState n := { view n g with
        par := Function.update (view n g).par x' 0
        mark := Function.update (view n g).mark x' 0
        numMarked := (view n g).numMarked - (view n g).mark x' } with hst₁
      have hv₁ : view n (Function.update (Function.update (Function.update g (.par x') 0)
          (.mark x') 0) .numMarked (g .numMarked - g (.mark x'))) = st₁ := by
        simp only [view_update_par, view_update_mark, view_update_numMarked, hst₁]
        rfl
      have hx_mem : x' ∈ rest[i].nodes := by rw [hx'_root]; exact rest[i].root_mem_nodes
      have hx_ne : ∀ y ∈ forestNodes (slots ++ rest'), y ≠ x' := fun y hy e =>
        hdisj y (e ▸ hx_mem) hy
      refine ⟨hxn, ⟨hxn, fits_zero w⟩, hxn, ⟨hxn, fits_zero w⟩, trivial,
        ⟨trivial, hfit.of_le ((Nat.sub_le _ _).trans hnm_le)⟩, ?_⟩
      refine Record.wp_mono (fun _ _ _ ⟨sl, a, b, c, d, e, f⟩ => ⟨sl, a, b, c, d, e,
        by simp only [ite_true] at f; omega⟩) (cont _ 6 (by simp) ?_ ?_ ?_ ?_ ?_ ?_ (by rw [hv₁]))
      · rw [hv₁]
        have := ValidSubtree.unmarkRoot (hrest _ hTmem).1 hTnd
          ((view n g).numMarked - (view n g).mark x')
        rw [← hx'_root] at this
        exact this
      · rw [hv₁]
        exact hs.frame rfl fun R hR => (hs.2.1 R hR).1.frame_nodes fun y hy => by
          have hy' := hx_ne y (hsub_slots y (mem_forestNodes_iff.mpr ⟨R, hR, hy⟩))
          simp [hst₁, hy']
      · rw [hv₁]
        refine ⟨rfl, rfl, rfl, rfl, rfl, fun y hy => ?_⟩
        have hy' : y ≠ x' := fun e => hy (hsubT y (e ▸ hx_mem))
        simp [hst₁, hy']
      · rw [hv₁]
        change (view n g).numMarked - (view n g).mark x' = markedCount st₁
        rw [hnm]
        exact (markedCount_unmark (st' := st₁) hin_x hmk (by simp [hst₁]) rfl fun y hy => by
          simp [hst₁, hy]).symm
      · rw [hv₁]; exact Nat.sub_le _ _
      · intro T hT
        rw [hv₁]
        refine ⟨(hrest T (hrest'_mem T hT)).1.frame (fun y hy => ?_) (fun y hy => ?_),
          fun h => absurd h (by decide)⟩
        · have hy' := hx_ne y (hsub_rest y (mem_forestNodes_iff.mpr ⟨T, hT, hy⟩))
          simp [hst₁, hy']
        · have hy' := hx_ne y (hsub_rest y (mem_forestNodes_iff.mpr ⟨T, hT,
            T.nodes_eq ▸ List.mem_cons_of_mem _ hy⟩))
          simp [hst₁, hy']

/-- **Gathering the table.** Scanning the slots `d, …, md` moves every tree of the table to the
root list, leaving the table empty, in at most `13` operations per slot. -/
theorem wp_gather {sz : ℕ} (hfit : Fits w n) :
    ∀ (k : ℕ) {g : Cell → ℕ} {d md : ℕ} {slots gs : List (FHTree n)},
      SlotInv n sz (view n g) slots md → (∀ T ∈ slots, d ≤ T.deg) → d + k = md + 1 →
      (∀ T ∈ gs, ValidRoot (view n g) none T) → RootList (view n g) gs →
      (view n g).numRoots = gs.length → (forestNodes (gs ++ slots)).Nodup →
      Record.wp (Cell.ok n) w (gather k d) (fun _ g' t => ∃ gs',
        (∀ T ∈ gs', ValidRoot (view n g') none T) ∧ RootList (view n g') gs' ∧
        (view n g').numRoots = gs'.length ∧ (forestNodes gs').Perm (forestNodes (gs ++ slots)) ∧
        gs'.length = gs.length + slots.length ∧ (∀ d ≤ n, (view n g').cons d = 0) ∧
        (view n g').key = (view n g).key ∧ (view n g').inHeap = (view n g).inHeap ∧
        (view n g').mark = (view n g).mark ∧ (view n g').numMarked = (view n g).numMarked ∧
        (view n g').sz = (view n g).sz ∧ t ≤ 13 * k) g
  | 0, g, d, md, slots, gs, hs, hge, hk, hgs, hrl, hnr, _ => by
    obtain ⟨rfl, hcons⟩ := hs.done_of_cleared fun d' hd' T hT he => by
      have := hge T hT; omega
    simp only [gather, Record.wp_pure]
    exact ⟨gs, hgs, hrl, hnr, by simp, by simp, hcons, trivial, trivial, trivial, trivial, trivial,
      by simp⟩
  | k + 1, g, d, md, slots, gs, hs, hge, hk, hgs, hrl, hnr, hnd => by
    have hdn : d ≤ n := by rcases hs.2.2.2.2.2 with h | h <;> omega
    simp only [gather, Record.wp_read_bind, Cell.ok]
    refine ⟨hdn, ?_⟩
    rcases hs.lookup hdn with ⟨h0, hnone⟩ | ⟨i, hi, hdi, hci, -, hno⟩
    · have h0' : g (.cons d) = 0 := h0
      simp only [h0', ite_true]
      refine Record.wp_mono ?_ (wp_gather hfit k hs (fun T hT => ?_) (by omega) hgs hrl hnr hnd)
      · rintro _ g' t ⟨gs', a, b, c, e, hl, f, h1, h2, h3, h4, h5, ht⟩
        exact ⟨gs', a, b, c, e, hl, f, h1, h2, h3, h4, h5, by omega⟩
      · have := hge T hT; have := hnone T hT; omega
    · set S := slots[i]
      have hci' : g (.cons d) = S.root.val + 1 := hci
      simp only [hci', Nat.add_one_ne_zero, ite_false, Record.wp_write_bind, Nat.add_sub_cancel,
        Cell.ok]
      refine ⟨⟨hdn, fits_zero w⟩, ?_⟩
      rw [Record.wp_bind]
      set g₁ := Function.update g (.cons d) 0
      have hv₁ : view n g₁ = { view n g with cons := Function.update (view n g).cons d 0 } :=
        view_update_cons g 0 d
      have hval₁ : ∀ R, ValidRoot (view n g) none R → ValidRoot (view n g₁) none R := fun R hR =>
        hv₁ ▸ hR.frame_nodes fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      have hSmem : S ∈ slots := List.getElem_mem hi
      have hs₁ := hs.step_collision hi hdi hdn hno (by rw [hv₁])
        fun R hR => hval₁ R (hs.2.1 R (List.mem_of_mem_eraseIdx hR)).1
      have hS₁ := hval₁ S (hs.2.1 S hSmem).1
      have hgs₁ : ∀ T ∈ gs, ValidRoot (view n g₁) none T := fun T hT => hval₁ T (hgs T hT)
      have hrl₁ : RootList (view n g₁) gs := by rw [hv₁]; exact hrl
      have hperm := forestNodes_eraseIdx_perm slots i hi
      have hP : (forestNodes ((S :: gs) ++ slots.eraseIdx i)).Perm (forestNodes (gs ++ slots)) := by
        rw [forestNodes_append, forestNodes_append]
        change (S.nodes ++ forestNodes gs ++ forestNodes (slots.eraseIdx i)).Perm _
        rw [List.append_assoc]
        exact (List.perm_append_comm_assoc _ _ _).trans (hperm.append_left _)
      have hnd' := hP.nodup_iff.mpr hnd
      have hnd_S : (forestNodes (S :: gs)).Nodup := by
        rw [forestNodes_append] at hnd'
        exact (List.nodup_append.mp hnd').1
      have hlen : gs.length + 1 ≤ n := by
        have h1 := forestNodes_length_ge (S :: gs)
        have h2 : (forestNodes (S :: gs)).length ≤ n := by simpa using hnd_S.length_le_card
        simp only [List.length_cons] at h1
        omega
      refine wp_addRoot (u := S.root) ?_ hfit (by rw [hv₁]; exact hfit.of_le (by simp; omega))
        fun g₂ t₂ ht₂ hadd => ?_
      · rcases hrl₁ with ⟨_, h0⟩ | ⟨m, rtail, hm, hcirc, -⟩
        exacts [Or.inl h0, Or.inr ⟨m, rtail, hm, hcirc⟩]
      obtain ⟨hall, hrl₂⟩ := RootList.addRoot hnd_S hS₁ hgs₁ hrl₁ hadd
      obtain ⟨l₂, r₂, m₂, heq₂⟩ := hadd.exists_eq
      have hs₂ : SlotInv n sz (view n g₂) (slots.eraseIdx i) md :=
        hs₁.frame (by rw [heq₂]) fun R hR =>
          hadd.validRoot_other hrl₁ hgs₁ hS₁.2.1 (hs₁.2.1 R hR).1
      refine Record.wp_mono ?_ (wp_gather hfit k hs₂ (fun T hT => ?_) (by omega) hall hrl₂
        (by rw [heq₂, hv₁, hnr]; rfl) hnd')
      · rintro _ g' t ⟨gs', a, b, c, e, hl, f, h1, h2, h3, h4, h5, ht⟩
        rw [heq₂] at h1 h2 h3 h4 h5
        have hlen' := List.length_eraseIdx_add_one hi
        exact ⟨gs', a, b, c, e.trans hP, by simp at hl; omega, f, h1, h2, h3, h4, h5, by omega⟩
      · have := hs.2.1 T (List.mem_of_mem_eraseIdx hT)
        have h1 := hge T (List.mem_of_mem_eraseIdx hT)
        have h2 := hno T hT
        omega

/-- **Extracting the minimum.** `extractMin n` implements `IndexedMinPQ.step` on `.extractMin`,
preserves the invariant, and costs at most `extractCharge` of the queue's size, amortized. -/
theorem wp_extractMin {K : ℕ} {g : Cell → ℕ} (hI : Inv n K g) (hfit : Fits w n) :
    Record.wp (Cell.ok n) w (extractMin n) (fun a g' t =>
      IndexedMinPQ.step (abs n g) .extractMin = (abs n g', a) ∧ Inv n K g' ∧
        t + potential n g' ≤
          extractCharge (IndexedMinPQ.dom (abs n g)).card + potential n g) g := by
  rcases minRoot_cases hI with h0 | ⟨z, rtail₀, hz, -⟩
  · have h0' : g .minRoot = 0 := h0
    simp only [extractMin, Record.wp_read_bind, h0', ite_true, Record.wp_pure, Cell.ok, true_and]
    refine ⟨?_, hI, by simp [extractCharge]; omega⟩
    simp [IndexedMinPQ.step, (FibRawInv.findMin_eq_none hI h0).2]
  have hz' : g .minRoot = z.val + 1 := hz
  have hzn := z.isLt
  obtain ⟨hfind, hsz_some, hkz⟩ := FibRawInv.findMin_eq_some hI hz
  have hI' := hI
  obtain ⟨ts, hts, hnd, hdom, hin, hkeys, hsz, hnr, hnm, hcons, hrl⟩ := hI'
  obtain ⟨m, rtail, hm, hcirc, hperm, hle⟩ := hrl.resolve_left fun ⟨_, h0⟩ => by
    change g .minRoot = 0 at h0; omega
  obtain rfl : m = z := Fin.ext (by change g .minRoot = m.val + 1 at hm; omega)
  obtain ⟨Tz, hTz, hTz_root⟩ := List.mem_map.mp (hperm.subset List.mem_cons_self)
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hTz
  -- The minimum root's tree, its children `cs`, and the other trees `E`.
  set T := ts[i] with hT_def
  have hT : T ∈ ts := List.getElem_mem hi
  set E := ts.eraseIdx i with hE
  have hpermTs : (T :: E).Perm ts := List.getElem_cons_eraseIdx_perm hi
  have hfs : (forestNodes ts).Perm (m :: (forestNodes T.children ++ forestNodes E)) := by
    refine (forestNodes_perm hpermTs).symm.trans ?_
    change (T.nodes ++ forestNodes E).Perm _
    rw [T.nodes_eq, hTz_root]
    rfl
  have hnd_all := hfs.nodup_iff.mp hnd
  have hm_cs : m ∉ forestNodes T.children ++ forestNodes E := (List.nodup_cons.mp hnd_all).1
  have hnd_cE := (List.nodup_cons.mp hnd_all).2
  have hcard : (IndexedMinPQ.dom (abs n g)).card = (forestNodes ts).length := by
    rw [← List.toFinset_card_of_nodup hnd]
    congr 1
    ext y
    simp [IndexedMinPQ.dom, hdom y]
  set s' := Function.update (abs n g) m none with hs'
  have hcard' : (IndexedMinPQ.dom s').card + 1 = (forestNodes ts).length := by
    rw [hs', IndexedMinPQ.dom_erase_update, ← hcard]
    exact Finset.card_erase_add_one (IndexedMinPQ.mem_dom_iff.mpr ⟨_, hsz_some⟩)
  have hlen_fs := hfs.length_eq
  simp only [List.length_cons, List.length_append] at hlen_fs
  -- The heap after detaching `m`.
  have hdeg_m : g (.deg m) = T.children.length := by
    have := ValidSubtree.deg_root (hts T hT).1
    rw [hTz_root] at this
    exact this
  have hnr_m : g .numRoots - 1 = rtail.length := by
    have h1 := hperm.length_eq
    change g .numRoots = ts.length at hnr
    simp only [List.length_cons, List.length_map] at h1
    omega
  have hcount : (view n g).sz ≤ n := by
    rw [hsz]; exact (Finset.card_le_univ _).trans (by simp)
  simp only [extractMin, Record.wp_read_bind, Record.wp_write_bind, hz', Nat.add_one_ne_zero,
    ite_false, Nat.add_sub_cancel, Function.update_apply, reduceCtorEq, Cell.ok, true_and,
    hdeg_m, hnr_m]
  refine ⟨hzn, ⟨hzn, fits_zero w⟩, hfit.of_le ((Nat.sub_le _ _).trans hcount), hzn, hzn, hzn, ?_⟩
  rw [Record.wp_bind]
  set g₁ := Function.update (Function.update g (.inHeap m) 0) .sz (g .sz - 1) with hg₁
  have hv₁ : view n g₁ = { view n g with
      inHeap := Function.update (view n g).inHeap m 0
      sz := (view n g).sz - 1 } := by
    simp only [hg₁, view_update_inHeap, view_update_sz]; rfl
  -- The children of `m`, in the order of their sibling list.
  obtain ⟨xs, hxs, hchainC, hheadC⟩ : ∃ xs : List (Fin n), xs.Perm (T.children.map FHTree.root) ∧
      RightChain (view n g).right xs ∧ ∀ y ∈ xs.head?, g (.child m) - 1 = y.val := by
    rcases ValidSubtree.child_root (hts T hT).1 with ⟨hnil, -⟩ | ⟨h, tail, hch, hcircC, hpermC⟩
    · exact ⟨[], by simp [hnil], trivial, by simp⟩
    · refine ⟨h :: tail, hpermC, hcircC.rightChain, fun y hy => ?_⟩
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
      subst hy
      rw [hTz_root] at hch
      change g (.child m) = _ at hch
      omega
  have hne_m : ∀ y ∈ forestNodes T.children ++ forestNodes E, y ≠ m := fun y hy e =>
    hm_cs (e ▸ hy)
  have hin_ne : ∀ y ∈ forestNodes T.children ++ forestNodes E, (view n g₁).inHeap y ≠ 0 :=
    fun y hy => by
      rw [hv₁]
      simp only [Function.update_of_ne (hne_m y hy)]
      exact (hin y).1.mpr ((hdom y).mp (hfs.symm.subset (List.mem_cons_of_mem _ hy)))
  have hvalid₁ : ∀ R : FHTree n, ValidSubtree (view n g) none R → (∀ y ∈ R.nodes, y ≠ m) →
      ValidSubtree (view n g₁) none R := fun R hR hRm =>
    hv₁ ▸ hR.frame (fun y hy => ⟨by simp [Function.update_of_ne (hRm y hy)], rfl, rfl, rfl, rfl⟩)
      (fun _ _ => ⟨rfl, rfl, rfl, Iff.rfl⟩)
  have hnm₁ : (view n g₁).numMarked = markedCount (view n g₁) := by
    rw [hv₁]
    refine hnm.trans (markedCount_congr fun y => ?_).symm
    by_cases hy : y = m
    · subst hy
      have := (hts T hT).2.2
      rw [hTz_root] at this
      simp [this]
    · simp [hy]
  have hcs_m : ∀ c ∈ T.children, ∀ y ∈ c.nodes, y ≠ m := fun c hc y hy =>
    hne_m y (List.mem_append_left _ (mem_forestNodes_iff.mpr ⟨c, hc, hy⟩))
  refine Record.wp_mono ?_ (wp_scatterList (sz := (IndexedMinPQ.dom s').card) (z := m) hfit true
    (Nat.lt_succ_self n) T.children.length (g := g₁) (xs := xs) (rest := T.children)
    (slots := []) (md := 0) (SlotInv.empty (by rw [hv₁]; exact hcons))
    (fun c hc => ⟨hvalid₁ c (ValidSubtree.sub (hts T hT).1 c hc) (hcs_m c hc),
      fun h => absurd h (by decide)⟩)
    hxs (by rw [hxs.length_eq, List.length_map]) (by rw [hv₁]; exact hchainC) hheadC
    (by simpa [T.nodes_eq, hTz_root] using forestNodes_nodup_tree hnd hT)
    (by simp; omega) (fun y hy => hin_ne y (List.mem_append_left _ hy)) hnm₁)
  rintro md₁ g₂ t₁ ⟨slots₁, hs₁, hp₁, hsc₁, hnm₂, hle₂, hc₁⟩
  rw [Record.wp_bind]
  have hE_disj : ∀ R ∈ E, ∀ y ∈ R.nodes, y ∉ forestNodes ([] ++ T.children) := by
    intro R hR y hy hy'
    rw [List.nil_append] at hy'
    exact (List.nodup_append.mp hnd_cE).2.2 y hy' y (mem_forestNodes_iff.mpr ⟨R, hR, hy⟩) rfl
  have hE_m : ∀ R ∈ E, ∀ y ∈ R.nodes, y ≠ m := fun R hR y hy =>
    hne_m y (List.mem_append_right _ (mem_forestNodes_iff.mpr ⟨R, hR, hy⟩))
  have hE_ts : ∀ R ∈ E, R ∈ ts := fun R hR => List.mem_of_mem_eraseIdx hR
  have hvalid₂ : ∀ R ∈ E, ValidRoot (view n g₂) none R := fun R hR =>
    hsc₁.validRoot ⟨hvalid₁ R (hts R (hE_ts R hR)).1 (hE_m R hR),
      by rw [hv₁]; exact (hts R (hE_ts R hR)).2.1, by rw [hv₁]; exact (hts R (hE_ts R hR)).2.2⟩
      (hE_disj R hR)
  have hrtail : rtail.Perm (E.map FHTree.root) := by
    have := hperm.trans (hpermTs.map FHTree.root).symm
    rw [List.map_cons, hTz_root] at this
    exact (List.perm_cons m).mp this
  have hchain0 := hcirc.rightChain
  have hchainR : RightChain (view n g₂).right rtail := by
    have h1 : RightChain (view n g).right rtail := by
      cases rtail with
      | nil => trivial
      | cons _ _ => exact hchain0.2
    refine h1.frame fun y hy => ?_
    obtain ⟨R, hR, rfl⟩ := List.mem_map.mp (hrtail.subset hy)
    obtain ⟨-, -, c, -, -, -⟩ := hsc₁.out _ (hE_disj R hR _ R.root_mem_nodes)
    rw [c, hv₁]
  have hheadR : ∀ y ∈ rtail.head?, g (.right m) = y.val := by
    intro y hy
    cases rtail with
    | nil => simp at hy
    | cons y' _ =>
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
      subst hy
      exact hchain0.1
  have hP₂ : (forestNodes (slots₁ ++ E)).Perm (forestNodes T.children ++ forestNodes E) := by
    rw [forestNodes_append]
    simpa using hp₁.append_right (forestNodes E)
  refine Record.wp_mono ?_ (wp_scatterList (sz := (IndexedMinPQ.dom s').card) (z := m) hfit false
    (Nat.lt_succ_self n) rtail.length (g := g₂) (xs := rtail) (rest := E) (slots := slots₁)
    (md := md₁) hs₁ (fun R hR => ⟨(hvalid₂ R hR).1, fun _ => ⟨(hvalid₂ R hR).2.1,
      (hvalid₂ R hR).2.2⟩⟩) hrtail rfl hchainR hheadR ((hP₂.cons m).nodup_iff.mpr hnd_all)
    (by rw [hP₂.length_eq]; simp; omega)
    (fun y hy => by rw [hsc₁.inHeap]; exact hin_ne y (List.mem_append_right _ hy)) hnm₂)
  rintro md₂ g₃ t₂ ⟨slots₂, hs₂, hp₂, hsc₂, hnm₃, hle₃, hc₂⟩
  simp only [Record.wp_write_bind, Cell.ok, true_and]
  refine ⟨fits_zero w, fits_zero w, ?_⟩
  rw [Record.wp_bind]
  have hP₃ : (forestNodes slots₂).Perm (forestNodes T.children ++ forestNodes E) := hp₂.trans hP₂
  have hs₄ : SlotInv n (IndexedMinPQ.dom s').card
      (view n (Function.update (Function.update g₃ .minRoot 0) .numRoots 0)) slots₂ md₂ :=
    hs₂.frame rfl fun R hR => (hs₂.2.1 R hR).1.frame_nodes fun _ _ =>
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine Record.wp_mono ?_ (wp_gather hfit (md₂ + 1) (d := 0) (gs := []) hs₄
    (fun _ _ => Nat.zero_le _) (by omega) (by simp) (Or.inl ⟨rfl, rfl⟩) rfl
    (by simpa using hP₃.nodup_iff.mpr hnd_cE))
  rintro _ g' t₃ ⟨gs', hval', hrl', hnr', hperm', hlen', hcons', hkey', hinh', hmark', hnmk',
    hsz', ht₃⟩
  simp only [Record.wp_pure]
  simp only [view_update_minRoot, view_update_numRoots] at hkey' hinh' hmark' hnmk' hsz'
  -- The new heap.
  have hP₄ : (forestNodes gs').Perm (forestNodes T.children ++ forestNodes E) := by
    simpa using hperm'.trans (by simpa using hP₃)
  have hkeyF : (view n g').key = (view n g).key := by
    rw [hkey', hsc₂.key, hsc₁.key, hv₁]
  have hinhF : (view n g').inHeap = Function.update (view n g).inHeap m 0 := by
    rw [hinh', hsc₂.inHeap, hsc₁.inHeap, hv₁]
  have hszF : (view n g').sz = (view n g).sz - 1 := by
    rw [hsz', hsc₂.sz, hsc₁.sz, hv₁]
  have hdom' : ∀ y, y ∈ forestNodes gs' ↔ (s' y).isSome := fun y => by
    rw [hP₄.mem_iff]
    by_cases hy : y = m
    · subst hy; simp [hs', hm_cs]
    · rw [hs', Function.update_of_ne hy, ← hdom y, hfs.mem_iff]
      simp [hy]
  have hfinal : FibRawInv n K s' (view n g') := by
    refine ⟨gs', hval', hP₄.nodup_iff.mpr hnd_cE, hdom', fun y => ?_, fun y ky hy => ?_, ?_,
      hnr', ?_, hcons', hrl'⟩
    · rw [hinhF]
      by_cases hym : y = m
      · subst hym; simp [hs']
      · rw [Function.update_of_ne hym, hs', Function.update_of_ne hym]; exact hin y
    · by_cases hym : y = m
      · subst hym; simp [hs'] at hy
      · rw [hs', Function.update_of_ne hym] at hy; rw [hkeyF]; exact hkeys y ky hy
    · rw [hszF, hsz]
      have := hcard'
      omega
    · rw [hnmk', hnm₃]
      exact markedCount_congr fun u => by rw [hinh', hmark']
  obtain ⟨hI', habs'⟩ := inv_of_fibRawInv hfinal
  refine ⟨?_, hI', ?_⟩
  · rw [habs']
    simp only [IndexedMinPQ.step, hfind, hs', hzn, dite_true, Prod.mk.injEq, Option.some.injEq,
      true_and]
    rfl
  · -- Cost: links are paid by the trees they remove; what remains is logarithmic.
    have hdz : T.children.length ≤ 2 * Nat.log 2 (IndexedMinPQ.dom (abs n g)).card + 1 := by
      have := (ValidSubtree.deg_bounds (hts T hT).1 (m := (IndexedMinPQ.dom (abs n g)).card)
        (by unfold FHTree.size; rw [T.nodes_eq, hcard]; simp; omega)).1
      exact this
    have hmd : md₂ ≤ 2 * Nat.log 2 (IndexedMinPQ.dom (abs n g)).card + 1 := by
      have h1 := hs₂.2.2.2.2.1
      have h2 : Nat.log 2 (IndexedMinPQ.dom s').card ≤
          Nat.log 2 (IndexedMinPQ.dom (abs n g)).card := Nat.log_mono_right (by omega)
      omega
    have hF := SlotInv.length_le hs₂
    have hR : ts.length = rtail.length + 1 := by
      have := hperm.length_eq; simp at this; omega
    have hnmF : (view n g').numMarked ≤ (view n g).numMarked := by
      have h1 : (view n g₁).numMarked = (view n g).numMarked := by rw [hv₁]
      omega
    simp only [Bool.false_eq_true, ite_false, ite_true, List.length_nil] at hc₁ hc₂ hlen'
    simp only [potential, credit, extractCharge, hnr']
    change _ ≤ _ + 24 * (g .numRoots + 2 * (view n g).numMarked)
    change g .numRoots = ts.length at hnr
    rw [hnr]
    omega

end Programs

end Cslib.DataStructure.PriorityQueue.FibonacciHeap
