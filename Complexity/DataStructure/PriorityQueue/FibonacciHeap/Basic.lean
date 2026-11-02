/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Memory.Record
public import Complexity.DataStructure.PriorityQueue.WordRAM.FibonacciHeap.Consolidate
public import Complexity.DataStructure.PriorityQueue.WordRAM.FibonacciHeap.Cut

/-!
# A Fibonacci heap as a record of named cells

This file sets up the Fibonacci heap [Fredman and Tarjan][FredmanTarjan1987] of
`Cslib.DataStructure.PriorityQueue.WordRAM.FibonacciHeap` as a program over a record of named
cells (`Record.spec`), rather than as hand-stepped word-RAM code. The record has the same struct
of arrays: per handle `key`, `par`, `child`, `left`, `right`, `deg`, `mark` and `inHeap`, a
consolidation table `cons`, and four scalars. `view` reads a record as the existing
`RawState n`, so the existing invariant `FibRawInv` and its forest lemmas apply unchanged.

* `absRaw` and `abs` decode the abstract `IndexedMinPQ.State n`; `Inv` is `FibRawInv` of the
  decoded state. The abstraction is a function, as `FibRawInv.unique` shows it must be.
* `potential` is `unit * (numRoots + 2 * numMarked)`, the textbook potential
  [Cormen et al., Section 19.1][CLRS2009] counted in record operations.
* `isEmpty`, `getKey` and `insert` are programs over the record, and their specifications
  (`wp_isEmpty`, `wp_getKey`, `wp_insert`) are stated with `Record.wp`: the operations are
  admissible, the result and the decoded state are those of `IndexedMinPQ.step`, the invariant is
  preserved, and the amortized cost is bounded.

The forest reasoning behind `insert` is `RootList.addRoot`, a statement about `RawState n`
alone: adding a valid root tree to a valid root list. The program-level proofs evaluate the
programs with `simp` and apply it.

The module adapts Renfei Zhou's native formalization (`WordRAM/FibonacciHeap`, in particular
`Program.lean` and `BasicOps.lean`) to the record level: his programs `insertCode` and
`addRootAndUpdateMin` become `insert` and `addRoot`, and their forest reasoning becomes
`FibRawInv.insert` and `RootList.addRoot`.

## Main definitions

* `Cell`, `Cell.ok`, `view`: the record's cells and its reading as `RawState n`.
* `absRaw`, `abs`, `Inv`, `potential`: abstraction, invariant and potential.
* `RootList`: the root-list part of `FibRawInv`.
* `spliceAfter`, `addRoot`, `isEmpty`, `getKey`, `insert`: record programs.

## Main results

* `view_update_key`, …: writes as updates of `RawState n`.
* `absRaw_eq_of_fibRawInv`: the invariant determines the abstract state.
* `RootList.addRoot`: adding a valid root tree keeps a valid root list.
* `wp_isEmpty`, `wp_getKey`, `wp_insert`: the first three operations.

## References

* [M. L. Fredman and R. E. Tarjan, *Fibonacci Heaps and Their Uses in Improved Network Optimization
  Algorithms*][FredmanTarjan1987]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Chapter 19][CLRS2009]
-/

@[expose] public section

namespace Cslib.DataStructure.PriorityQueue.FibonacciHeap

open Cslib.WordRAM Cslib.DataStructure Cslib.DataStructure.PriorityQueue
open Cslib.DataStructure.PriorityQueue.WordRAM.FibonacciHeap

/-! ## The record -/

/-- The cells of a Fibonacci heap: eight per-handle arrays, the consolidation table and four
scalars. Indices are words; `Cell.ok` says which cells exist. -/
inductive Cell where
  /-- The key of a handle. -/
  | key (v : ℕ)
  /-- The parent of a handle: `0` for a root, `p + 1` for parent `p`. -/
  | par (v : ℕ)
  /-- Some child of a handle: `0` for none, `c + 1` for child `c`. -/
  | child (v : ℕ)
  /-- The predecessor of a handle in its circular sibling list. -/
  | left (v : ℕ)
  /-- The successor of a handle in its circular sibling list. -/
  | right (v : ℕ)
  /-- The number of children of a handle. -/
  | deg (v : ℕ)
  /-- The cascading-cut mark of a handle. -/
  | mark (v : ℕ)
  /-- Whether a handle is present. -/
  | inHeap (v : ℕ)
  /-- The consolidation table entry for degree `d`: `0` for none, `u + 1` for root `u`. -/
  | cons (d : ℕ)
  /-- The minimum root: `0` for an empty heap, `m + 1` for root `m`. -/
  | minRoot
  /-- The number of roots. -/
  | numRoots
  /-- The number of marked handles. -/
  | numMarked
  /-- The number of handles present. -/
  | sz
  deriving DecidableEq

/-- The cells of a heap on `n` handles: array entries below `n`, table entries up to `n`, and the
scalars. -/
def Cell.ok (n : ℕ) : Cell → Prop
  | .key v | .par v | .child v | .left v | .right v | .deg v | .mark v | .inHeap v => v < n
  | .cons d => d ≤ n
  | .minRoot | .numRoots | .numMarked | .sz => True

instance (n : ℕ) : DecidablePred (Cell.ok n) := fun c => by
  cases c <;> unfold Cell.ok <;> infer_instance

/-- The record as the existing raw view of a Fibonacci heap. -/
def view (n : ℕ) (g : Cell → ℕ) : RawState n where
  key v := g (.key v)
  par v := g (.par v)
  child v := g (.child v)
  left v := g (.left v)
  right v := g (.right v)
  deg v := g (.deg v)
  mark v := g (.mark v)
  inHeap v := g (.inHeap v)
  cons d := g (.cons d)
  minRoot := g .minRoot
  numRoots := g .numRoots
  numMarked := g .numMarked
  sz := g .sz

/-- Programs over the heap's record. -/
abbrev Prog (α : Type) : Type := Record.Prog Cell α

/-- Read a cell. -/
abbrev rd (c : Cell) : Prog ℕ := Record.read c

/-- Write a cell. -/
abbrev wr (c : Cell) (x : ℕ) : Prog Unit := Record.write c x

/-! ## Writes as updates of the raw view -/

section View

variable {n : ℕ} (g : Cell → ℕ) (x : ℕ)

@[simp] theorem view_update_key (v : Fin n) :
    view n (Function.update g (.key v) x) =
      { view n g with key := Function.update (view n g).key v x } := by
  simp only [view]
  congr 1
  funext u
  simp [Function.update_apply, Fin.val_inj]

@[simp] theorem view_update_par (v : Fin n) :
    view n (Function.update g (.par v) x) =
      { view n g with par := Function.update (view n g).par v x } := by
  simp only [view]
  congr 1
  funext u
  simp [Function.update_apply, Fin.val_inj]

@[simp] theorem view_update_child (v : Fin n) :
    view n (Function.update g (.child v) x) =
      { view n g with child := Function.update (view n g).child v x } := by
  simp only [view]
  congr 1
  funext u
  simp [Function.update_apply, Fin.val_inj]

@[simp] theorem view_update_left (v : Fin n) :
    view n (Function.update g (.left v) x) =
      { view n g with left := Function.update (view n g).left v x } := by
  simp only [view]
  congr 1
  funext u
  simp [Function.update_apply, Fin.val_inj]

@[simp] theorem view_update_right (v : Fin n) :
    view n (Function.update g (.right v) x) =
      { view n g with right := Function.update (view n g).right v x } := by
  simp only [view]
  congr 1
  funext u
  simp [Function.update_apply, Fin.val_inj]

@[simp] theorem view_update_deg (v : Fin n) :
    view n (Function.update g (.deg v) x) =
      { view n g with deg := Function.update (view n g).deg v x } := by
  simp only [view]
  congr 1
  funext u
  simp [Function.update_apply, Fin.val_inj]

@[simp] theorem view_update_mark (v : Fin n) :
    view n (Function.update g (.mark v) x) =
      { view n g with mark := Function.update (view n g).mark v x } := by
  simp only [view]
  congr 1
  funext u
  simp [Function.update_apply, Fin.val_inj]

@[simp] theorem view_update_inHeap (v : Fin n) :
    view n (Function.update g (.inHeap v) x) =
      { view n g with inHeap := Function.update (view n g).inHeap v x } := by
  simp only [view]
  congr 1
  funext u
  simp [Function.update_apply, Fin.val_inj]

@[simp] theorem view_update_cons (d : ℕ) :
    view n (Function.update g (.cons d) x) =
      { view n g with cons := Function.update (view n g).cons d x } := by
  simp only [view]
  congr 1
  funext e
  simp [Function.update_apply]

@[simp] theorem view_update_minRoot :
    view n (Function.update g .minRoot x) = { view n g with minRoot := x } := rfl

@[simp] theorem view_update_numRoots :
    view n (Function.update g .numRoots x) = { view n g with numRoots := x } := rfl

@[simp] theorem view_update_numMarked :
    view n (Function.update g .numMarked x) = { view n g with numMarked := x } := rfl

@[simp] theorem view_update_sz :
    view n (Function.update g .sz x) = { view n g with sz := x } := rfl

end View

/-! ## Abstraction, invariant and potential -/

/-- The priority queue a raw state stores: present handles with their keys. -/
def absRaw {n : ℕ} (st : RawState n) : IndexedMinPQ.State n :=
  fun v => if st.inHeap v = 0 then none else some (st.key v)

/-- The priority queue a record stores. -/
abbrev abs (n : ℕ) (g : Cell → ℕ) : IndexedMinPQ.State n := absRaw (view n g)

/-- The implementation invariant: the existing Fibonacci-heap invariant, of the decoded queue. -/
def Inv (n K : ℕ) (g : Cell → ℕ) : Prop := FibRawInv n K (abs n g) (view n g)

/-- The invariant determines the stored queue. -/
theorem absRaw_eq_of_fibRawInv {n K : ℕ} {s : IndexedMinPQ.State n} {st : RawState n}
    (h : FibRawInv n K s st) : absRaw st = s := by
  obtain ⟨_, _, _, _, hin, hkeys, _⟩ := h
  funext v
  cases hs : s v with
  | none =>
    have : st.inHeap v = 0 := by
      by_contra h0
      simpa [hs] using (hin v).1.mp h0
    simp [absRaw, this]
  | some k =>
    have h0 : st.inHeap v ≠ 0 := (hin v).1.mpr (by simp [hs])
    simp [absRaw, h0, (hkeys v k hs).1]

/-- A record satisfies the invariant when its raw view satisfies `FibRawInv` of any queue. -/
theorem inv_of_fibRawInv {n K : ℕ} {s : IndexedMinPQ.State n} {g : Cell → ℕ}
    (h : FibRawInv n K s (view n g)) : Inv n K g ∧ abs n g = s := by
  have he := absRaw_eq_of_fibRawInv h
  refine ⟨?_, he⟩
  unfold Inv abs
  rw [he]
  exact h

/-- Credits per root and per two marks, in record operations. -/
abbrev credit : ℕ := 24

/-- The Fibonacci-heap potential `credit * (numRoots + 2 * numMarked)`. -/
def potential (n : ℕ) (g : Cell → ℕ) : ℕ :=
  credit * ((view n g).numRoots + 2 * (view n g).numMarked)

/-! ## The root list -/

/-- The root-list part of `FibRawInv`: an empty heap has no minimum root; otherwise the roots
form a circular list headed by the minimum root `m`. -/
def RootList {n : ℕ} (st : RawState n) (ts : List (FHTree n)) : Prop :=
  (ts = [] ∧ st.minRoot = 0) ∨
    ∃ (m : Fin n) (rtail : List (Fin n)),
      st.minRoot = m.val + 1 ∧
      IsCircList st.left st.right (m :: rtail) ∧
      (m :: rtail).Perm (ts.map FHTree.root) ∧
      ∀ T ∈ ts, IndexedMinPQ.PrioLE (m, st.key m) (T.root, st.key T.root)

/-- The effect of adding root `u`: on an empty heap, `u` forms the root list alone; otherwise `u`
is spliced in after the minimum root `m` and becomes the minimum if it precedes `m`. Either way the
number of roots grows by one. -/
def AddsRoot {n : ℕ} (st : RawState n) (u : Fin n) (st' : RawState n) : Prop :=
  (st.minRoot = 0 ∧
    st' = { st with
      left := Function.update st.left u u.val
      right := Function.update st.right u u.val
      minRoot := u.val + 1
      numRoots := st.numRoots + 1 }) ∨
  ∃ m r : Fin n, st.minRoot = m.val + 1 ∧ st.right m = r.val ∧
    st' = { st with
      left := Function.update (Function.update st.left u m.val) r u.val
      right := Function.update (Function.update st.right u r.val) m u.val
      minRoot := if IndexedMinPQ.PrioLT (u, st.key u) (m, st.key m) then u.val + 1 else m.val + 1
      numRoots := st.numRoots + 1 }

/-- Adding a valid root tree to a forest of valid root trees with a valid root list keeps every tree
a valid root and the root list valid. Only roots change their sibling pointers, and
`ValidSubtree` reads sibling pointers only below the root. -/
theorem RootList.addRoot {n : ℕ} {st st' : RawState n} {T_u : FHTree n} {ts : List (FHTree n)}
    (hnd : (forestNodes (T_u :: ts)).Nodup) (hTu : ValidRoot st none T_u)
    (hts : ∀ T ∈ ts, ValidRoot st none T) (hrl : RootList st ts)
    (hadd : AddsRoot st T_u.root st') :
    (∀ T ∈ T_u :: ts, ValidRoot st' none T) ∧ RootList st' (T_u :: ts) := by
  have hvalid : ∀ T ∈ T_u :: ts, ValidRoot st none T := by
    intro T hT
    rcases List.mem_cons.mp hT with rfl | hT
    exacts [hTu, hts T hT]
  -- A strict descendant is no root, so the frame of `ValidRoot` excludes the changed pointers.
  have hdesc : ∀ T ∈ T_u :: ts, ∀ x ∈ forestNodes T.children, ∀ R ∈ T_u :: ts, x ≠ R.root :=
    fun T hT x hx R hR => descendant_ne_root_of_nodup hnd hT hR hx
  have hroot_ts : ∀ x ∈ ts.map FHTree.root, ∃ R ∈ T_u :: ts, x = R.root := fun x hx => by
    obtain ⟨R, hR, rfl⟩ := List.mem_map.mp hx
    exact ⟨R, List.mem_cons_of_mem _ hR, rfl⟩
  have hu_ts : T_u.root ∉ ts.map FHTree.root := fun hx => by
    obtain ⟨R, hR, hRu⟩ := List.mem_map.mp hx
    obtain ⟨-, -, hdisj⟩ := List.nodup_append.mp hnd
    exact hdisj _ T_u.root_mem_nodes _
      (mem_forestNodes_iff.mpr ⟨R, hR, hRu ▸ R.root_mem_nodes⟩) rfl
  rcases hadd with ⟨h0, rfl⟩ | ⟨m, r, hm, hr, rfl⟩
  · have hts0 : ts = [] := by
      rcases hrl with ⟨h, _⟩ | ⟨_, _, hm', _⟩
      · exact h
      · omega
    subst hts0
    refine ⟨fun T hT => (hvalid T hT).frame_tree (fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
      fun x hx => ?_, Or.inr ⟨T_u.root, [], rfl, IsCircList.singleton _ _ _, by simp,
        fun T hT => by simp only [List.mem_singleton] at hT; subst hT; exact .refl _⟩⟩
    have hx := hdesc T hT x hx T_u List.mem_cons_self
    simp [Function.update_of_ne hx]
  · obtain ⟨m', rtail, hm', hcirc, hperm, hle⟩ := hrl.resolve_left fun ⟨_, h0⟩ => by omega
    obtain rfl : m' = m := Fin.ext (by omega)
    obtain ⟨r', hr', hr'_mem⟩ := hcirc.right_head
    obtain rfl : r' = r := Fin.ext (by omega)
    obtain ⟨Rm, hRm, hRm_eq⟩ := hroot_ts m' (hperm.subset List.mem_cons_self)
    obtain ⟨Rr, hRr, hRr_eq⟩ := hroot_ts r' (hperm.subset hr'_mem)
    have hu_mr : T_u.root ∉ m' :: rtail := fun h => hu_ts (hperm.subset h)
    have hcirc' := hcirc.insertAfter hu_mr hr
    refine ⟨fun T hT => (hvalid T hT).frame_tree (fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
      fun x hx => ?_, Or.inr ?_⟩
    · have hxu := hdesc T hT x hx T_u List.mem_cons_self
      have hxm := hdesc T hT x hx Rm hRm
      have hxr := hdesc T hT x hx Rr hRr
      rw [← hRm_eq] at hxm
      rw [← hRr_eq] at hxr
      simp [Function.update_of_ne hxu, Function.update_of_ne hxm, Function.update_of_ne hxr]
    · have hperm' : (T_u.root :: m' :: rtail).Perm ((T_u :: ts).map FHTree.root) :=
        List.Perm.cons _ hperm
      by_cases hlt : IndexedMinPQ.PrioLT (T_u.root, st.key T_u.root) (m', st.key m')
      · refine ⟨T_u.root, rtail ++ [m'], by simp [hlt], ?_, ?_, fun T hT => ?_⟩
        · simpa using hcirc'.rotate_one
        · exact (List.Perm.cons _ (List.perm_append_singleton _ _)).trans hperm'
        · rcases List.mem_cons.mp hT with rfl | hT
          · exact .refl _
          · exact hlt.le.trans (hle T hT)
      · refine ⟨m', T_u.root :: rtail, by simp [hlt], hcirc', (List.Perm.swap _ _ _).trans hperm',
          fun T hT => ?_⟩
        rcases List.mem_cons.mp hT with rfl | hT
        · exact IndexedMinPQ.not_prioLT_iff_prioLE.mp hlt
        · exact hle T hT

/-- Adding a root changes only the root list and the number of roots. -/
theorem AddsRoot.exists_eq {n : ℕ} {st st' : RawState n} {u : Fin n} (h : AddsRoot st u st') :
    ∃ (left right : Fin n → ℕ) (minRoot : ℕ), st' = { st with
      left := left
      right := right
      minRoot := minRoot
      numRoots := st.numRoots + 1 } := by
  rcases h with ⟨_, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;> exact ⟨_, _, _, rfl⟩

/-- A new handle `v` with key `k`, as a childless unmarked root, before it joins the root list. -/
def newNode {n : ℕ} (st : RawState n) (v : Fin n) (k : ℕ) : RawState n :=
  { st with
    key := Function.update st.key v k
    par := Function.update st.par v 0
    child := Function.update st.child v 0
    deg := Function.update st.deg v 0
    mark := Function.update st.mark v 0
    inHeap := Function.update st.inHeap v 1 }

/-- **Insertion preserves the invariant.** Creating `v` as a singleton tree and adding it to the
root list stores `v` with key `k`, with one more root and one more handle. -/
theorem FibRawInv.insert {n K : ℕ} {s : IndexedMinPQ.State n} {st st' : RawState n} {v : Fin n}
    {k : ℕ} (h : FibRawInv n K s st) (hv : s v = none) (hk : k ≤ K)
    (hadd : AddsRoot (newNode st v k) v st') :
    FibRawInv n K (Function.update s v (some k)) { st' with sz := st'.sz + 1 } := by
  obtain ⟨ts, hts, hnd, hdom, hin, hkeys, hsz, hnr, hnm, hcons, hrl⟩ := h
  have hv_fn : v ∉ forestNodes ts := fun hm => by simpa [hv] using (hdom v).mp hm
  have hin_v : st.inHeap v = 0 := by
    by_contra h0
    simpa [hv] using (hin v).1.mp h0
  have hnd' : (forestNodes (.node v [] :: ts)).Nodup := by
    simpa [forestNodes, FHTree.nodes] using ⟨hv_fn, hnd⟩
  have hne : ∀ T ∈ ts, ∀ x ∈ T.nodes, x ≠ v := fun T hT x hx hxv =>
    hv_fn (mem_forestNodes_iff.mpr ⟨T, hT, hxv ▸ hx⟩)
  have hTv : ValidRoot (newNode st v k) none (.node v []) :=
    ValidRoot.singleton (by simp [newNode]) (by simp [newNode])
      (by simp [newNode]) (by simp [newNode]) (by simp [newNode])
  have hts₁ : ∀ T ∈ ts, ValidRoot (newNode st v k) none T := fun T hT =>
    (hts T hT).frame_tree (fun x hx => by
      simp [newNode, Function.update_of_ne (hne T hT x hx)]) fun _ _ => ⟨rfl, rfl⟩
  have hrl₁ : RootList (newNode st v k) ts := by
    rcases hrl with h0 | ⟨m, rtail, hm, hcirc, hperm, hle⟩
    · exact Or.inl h0
    · have hroot : ∀ T ∈ ts, T.root ≠ v := fun T hT => hne T hT _ T.root_mem_nodes
      obtain ⟨Tm, hTm, rfl⟩ := List.mem_map.mp (hperm.subset List.mem_cons_self)
      refine Or.inr ⟨Tm.root, rtail, hm, hcirc, hperm, fun T hT => ?_⟩
      simpa [newNode, Function.update_of_ne (hroot T hT),
        Function.update_of_ne (hroot Tm hTm)] using hle T hT
  obtain ⟨hts', hrl'⟩ := RootList.addRoot hnd' hTv hts₁ hrl₁ hadd
  obtain ⟨left, right, minRoot, rfl⟩ := hadd.exists_eq
  refine ⟨.node v [] :: ts, fun T hT => (hts' T hT).frame_tree
    (fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩) (fun _ _ => ⟨rfl, rfl⟩), hnd', fun x => ?_,
    fun x => ?_, fun x kx hx => ?_, ?_, by simp [newNode, hnr], ?_,
    fun d hd => hcons d hd, hrl'⟩
  · by_cases hxv : x = v
    · subst hxv; simp [forestNodes, FHTree.nodes]
    · simp [forestNodes, FHTree.nodes, hxv, hdom x]
  · by_cases hxv : x = v
    · subst hxv; simp [newNode]
    · simpa [newNode, hxv] using hin x
  · by_cases hxv : x = v
    · subst hxv
      simp only [Function.update_self, Option.some.injEq] at hx
      subst hx
      simp [newNode, hk]
    · rw [Function.update_of_ne hxv] at hx
      simpa [newNode, hxv] using hkeys x kx hx
  · have hvd : v ∉ IndexedMinPQ.dom s := IndexedMinPQ.notMem_dom_iff.mpr hv
    simp [newNode, hsz, Finset.card_insert_of_notMem hvd]
  · refine hnm.trans (markedCount_congr fun x => ?_).symm
    by_cases hxv : x = v
    · subst hxv; simp [newNode, hin_v]
    · simp [newNode, hxv]

/-! ## Programs -/

/-- Splice `u` into a circular list right after `h`. -/
def spliceAfter (h u : ℕ) : Prog Unit := do
  let r ← rd (.right h)
  wr (.left u) h
  wr (.left r) u
  wr (.right u) r
  wr (.right h) u

/-- Add root `u` to the root list, updating the minimum root and the number of roots. -/
def addRoot (u : ℕ) : Prog Unit := do
  let m ← rd .minRoot
  if m = 0 then
    wr (.left u) u
    wr (.right u) u
    wr .minRoot (u + 1)
  else
    spliceAfter (m - 1) u
    let ku ← rd (.key u)
    let km ← rd (.key (m - 1))
    if IndexedMinPQ.RawPrioLT (u, ku) (m - 1, km) then wr .minRoot (u + 1)
  let r ← rd .numRoots
  wr .numRoots (r + 1)

/-- Whether the heap is empty: whether there is no minimum root. -/
def isEmpty : Prog Bool := do
  let m ← rd .minRoot
  pure (decide (m = 0))

/-- The key of handle `v`, if present. -/
def getKey (v : ℕ) : Prog (Option ℕ) := do
  let b ← rd (.inHeap v)
  if b = 0 then pure none else do
    let k ← rd (.key v)
    pure (some k)

/-- Insert handle `v` with key `k` as a new singleton root. -/
def insert (v k : ℕ) : Prog Unit := do
  wr (.key v) k
  wr (.par v) 0
  wr (.child v) 0
  wr (.deg v) 0
  wr (.mark v) 0
  wr (.inHeap v) 1
  addRoot v
  let c ← rd .sz
  wr .sz (c + 1)

/-! ## Evaluating the programs -/

section Programs

variable {n w : ℕ}

/-- Adding a root evaluates to `AddsRoot` in at most eleven operations. -/
theorem wp_addRoot {g : Cell → ℕ} {u : Fin n}
    (hroot : (view n g).minRoot = 0 ∨ ∃ (m : Fin n) (rtail : List (Fin n)),
      (view n g).minRoot = m.val + 1 ∧ IsCircList (view n g).left (view n g).right (m :: rtail))
    (hfit : Fits w n) (hnr : Fits w ((view n g).numRoots + 1))
    {Q : Unit → (Cell → ℕ) → ℕ → Prop}
    (hQ : ∀ g' t, t ≤ 11 → AddsRoot (view n g) u (view n g') → Q () g' t) :
    Record.wp (Cell.ok n) w (addRoot u) Q g := by
  have hu := u.isLt
  rcases hroot with h0 | ⟨m, rtail, hm, hcirc⟩
  · have h0' : g .minRoot = 0 := h0
    simp only [addRoot, Record.wp_bind, Record.wp_read, Record.wp_write, h0', ite_true,
      Function.update_apply, reduceCtorEq, ite_false, Cell.ok, true_and]
    refine ⟨⟨hu, hfit.of_le hu.le⟩, ⟨hu, hfit.of_le hu.le⟩, hfit.of_le hu, hnr,
      hQ _ _ (by omega) (Or.inl ⟨h0, ?_⟩)⟩
    simp only [view_update_left, view_update_right, view_update_minRoot, view_update_numRoots]
    rfl
  · obtain ⟨r, hr, -⟩ := hcirc.right_head
    have hm' : g .minRoot = m.val + 1 := hm
    have hr' : g (.right m) = r.val := hr
    have hmn := m.isLt
    have hrn := r.isLt
    simp only [addRoot, spliceAfter, Record.wp_bind, Record.wp_read, Record.wp_write, hm',
      Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel, hr', Function.update_apply,
      reduceCtorEq, Cell.ok, true_and]
    refine ⟨hmn, ⟨hu, hfit.of_le hmn.le⟩, ⟨hrn, hfit.of_le hu.le⟩, ⟨hu, hfit.of_le hrn.le⟩,
      ⟨hmn, hfit.of_le hu.le⟩, hu, hmn, ?_⟩
    have hview : ∀ x, view n (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update g (.left u) m) (.left r) u) (.right u) r) (.right m) u)
          .minRoot x) .numRoots (g .numRoots + 1)) = { view n g with
        left := Function.update (Function.update (view n g).left u m.val) r u.val
        right := Function.update (Function.update (view n g).right u r.val) m u.val
        minRoot := x
        numRoots := (view n g).numRoots + 1 } := fun x => by
      simp only [view_update_left, view_update_right, view_update_minRoot, view_update_numRoots]
      rfl
    by_cases hlt : IndexedMinPQ.RawPrioLT (↑u, g (Cell.key ↑u)) (↑m, g (Cell.key ↑m))
    · simp only [hlt, ite_true, Record.wp_bind, Record.wp_read, Record.wp_write,
        Function.update_apply, reduceCtorEq, ite_false, Cell.ok, true_and]
      refine ⟨hfit.of_le hu, hnr, hQ _ _ (by omega) (Or.inr ⟨m, r, hm, hr, ?_⟩)⟩
      simp only [show IndexedMinPQ.PrioLT (u, (view n g).key u) (m, (view n g).key m) from hlt,
        ite_true]
      exact hview _
    · simp only [hlt, ite_false, Record.wp_bind, Record.wp_read, Record.wp_write,
        Function.update_apply, reduceCtorEq, Cell.ok, true_and]
      refine ⟨hnr, hQ _ _ (by omega) (Or.inr ⟨m, r, hm, hr, ?_⟩)⟩
      simp only [show ¬IndexedMinPQ.PrioLT (u, (view n g).key u) (m, (view n g).key m) from hlt,
        ite_false, view_update_left, view_update_right, view_update_numRoots, ← hm]
      rfl

/-- The root list of a valid heap is empty or headed by the minimum root, as `addRoot` needs. -/
theorem minRoot_cases {K : ℕ} {s : IndexedMinPQ.State n} {st : RawState n}
    (h : FibRawInv n K s st) : st.minRoot = 0 ∨ ∃ (m : Fin n) (rtail : List (Fin n)),
      st.minRoot = m.val + 1 ∧ IsCircList st.left st.right (m :: rtail) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hrl⟩ := h
  rcases hrl with ⟨_, h0⟩ | ⟨m, rtail, hm, hcirc, _⟩
  exacts [Or.inl h0, Or.inr ⟨m, rtail, hm, hcirc⟩]

/-- With a handle absent, there is room for one more root and one more handle. -/
theorem counts_lt_of_absent {K : ℕ} {s : IndexedMinPQ.State n} {st : RawState n}
    (h : FibRawInv n K s st) {v : Fin n} (hv : s v = none) :
    st.numRoots + 1 ≤ n ∧ st.sz + 1 ≤ n := by
  obtain ⟨ts, _, hnd, hdom, _, _, hsz, hnr, _⟩ := h
  have hv_fn : v ∉ forestNodes ts := fun hm => by simpa [hv] using (hdom v).mp hm
  have hlen : (v :: forestNodes ts).length ≤ n := by
    simpa using (List.nodup_cons.mpr ⟨hv_fn, hnd⟩).length_le_card
  have hts := forestNodes_length_ge ts
  have hdom_lt : (IndexedMinPQ.dom s).card < n := by
    have hsub : IndexedMinPQ.dom s ⊂ Finset.univ :=
      Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, fun he => by
        have := IndexedMinPQ.notMem_dom_iff.mpr hv
        rw [he] at this
        exact this (Finset.mem_univ v)⟩
    simpa using Finset.card_lt_card hsub
  simp only [List.length_cons] at hlen
  omega

/-- **Emptiness.** `isEmpty` reads the minimum root once. -/
theorem wp_isEmpty {K : ℕ} {g : Cell → ℕ} (hI : Inv n K g) :
    Record.wp (Cell.ok n) w isEmpty (fun b g' t =>
      b = decide (IndexedMinPQ.dom (abs n g) = ∅) ∧ g' = g ∧ t = 1) g := by
  simp only [isEmpty, Record.wp_read_bind, Record.wp_pure, Cell.ok, true_and, and_true]
  refine decide_eq_decide.mpr ⟨fun h0 => (FibRawInv.findMin_eq_none hI h0).1, fun hemp => ?_⟩
  rcases minRoot_cases hI with h0 | ⟨m, _, hm, _⟩
  · exact h0
  · have hmem := IndexedMinPQ.mem_dom_iff.mpr ⟨_, (FibRawInv.findMin_eq_some hI hm).2.1⟩
    simp [hemp] at hmem

/-- **Key lookup.** `getKey v` reads the presence flag and, if present, the key. No invariant is
needed: the abstraction reads the same two cells. -/
theorem wp_getKey {g : Cell → ℕ} (v : Fin n) :
    Record.wp (Cell.ok n) w (getKey v) (fun a g' t => a = abs n g v ∧ g' = g ∧ t ≤ 2) g := by
  have hv := v.isLt
  by_cases h0 : g (.inHeap v) = 0
  · simp only [getKey, Record.wp_read_bind, h0, ite_true, Record.wp_pure, Cell.ok]
    exact ⟨hv, by simp [abs, absRaw, view, h0], trivial, by omega⟩
  · simp only [getKey, Record.wp_read_bind, h0, ite_false, Record.wp_pure, Cell.ok]
    exact ⟨hv, hv, by simp [abs, absRaw, view, h0], trivial, by omega⟩

/-- **Insertion.** `insert v k` stores `v` with key `k`, preserves the invariant, and costs at most
`19` operations plus one credit for the new root. -/
theorem wp_insert {K : ℕ} {g : Cell → ℕ} {v : Fin n} {k : ℕ} (hI : Inv n K g)
    (hv : abs n g v = none) (hk : k ≤ K) (hn : Fits w n) (hK : Fits w K) :
    Record.wp (Cell.ok n) w (insert v k) (fun _ g' t =>
      abs n g' = Function.update (abs n g) v (some k) ∧ Inv n K g' ∧
        t + potential n g' ≤ 19 + credit + potential n g) g := by
  have hvn := v.isLt
  obtain ⟨hnr, hsz⟩ := counts_lt_of_absent hI hv
  simp only [insert, Record.wp_bind, Record.wp_write, Cell.ok, true_and]
  refine ⟨⟨hvn, hK.of_le hk⟩, ⟨hvn, fits_zero w⟩, ⟨hvn, fits_zero w⟩, ⟨hvn, fits_zero w⟩,
    ⟨hvn, fits_zero w⟩, ⟨hvn, hn.of_le (by omega)⟩, ?_⟩
  refine wp_addRoot ?_ hn ?_ fun g₂ t ht hadd => ?_
  · simpa only [view_update_key, view_update_par, view_update_child, view_update_deg,
      view_update_mark, view_update_inHeap] using minRoot_cases hI
  · simpa only [view_update_key, view_update_par, view_update_child, view_update_deg,
      view_update_mark, view_update_inHeap] using hn.of_le hnr
  simp only [view_update_key, view_update_par, view_update_child, view_update_deg,
    view_update_mark, view_update_inHeap] at hadd
  change AddsRoot (newNode (view n g) v k) v (view n g₂) at hadd
  obtain ⟨left, right, minRoot, heq⟩ := hadd.exists_eq
  have hsz₂ : g₂ .sz = (view n g).sz := congrArg RawState.sz heq
  simp only [Record.wp_read, Cell.ok, true_and, hsz₂]
  refine ⟨hn.of_le hsz, ?_⟩
  have hinv := FibRawInv.insert hI hv hk hadd
  obtain ⟨hI', habs'⟩ := inv_of_fibRawInv (g := Function.update g₂ .sz ((view n g).sz + 1))
    (by rw [view_update_sz, ← hsz₂]; exact hinv)
  refine ⟨habs', hI', ?_⟩
  have hnr₂ : (view n g₂).numRoots = (view n g).numRoots + 1 := by rw [heq]; rfl
  have hnm₂ : (view n g₂).numMarked = (view n g).numMarked := by rw [heq]; rfl
  simp only [potential, credit, view_update_sz, hnr₂, hnm₂]
  omega

end Programs

end Cslib.DataStructure.PriorityQueue.FibonacciHeap
