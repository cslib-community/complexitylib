/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.TreeDecomposition.BagMask
public import CslibFrontier.Algorithms.Lean.TreeDecomposition.IndependentSet
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# An executable FPT program for maximum-weight independent set

`mwisFPT R w L` is a `TimeM ℕ` program that computes the maximum total weight of an independent
set of `G`, given a rooted tree decomposition `R : G.RootedTreeDecomposition n`, vertex weights
`w : V → ℕ` and an ordering `L` of the bags (`IsBagOrder R L`). It materializes the tables of the
dynamic program `mwisValue` of `CslibFrontier.Algorithms.Lean.TreeDecomposition.IndependentSet` as
arrays indexed by bit masks, stores them in a `Vector` over the nodes, and charges its ticks
inside the loops that do the work. `ret_mwisFPT` proves that it returns `mwisValue R w`, so it
returns the optimum (`isGreatest_mwisFPT`). `time_mwisFPT` gives its exact tick count as a function
of the bag sizes, and `time_mwisFPT_le` bounds it by
`(n + 1) · 2 ^ (k + 1) · (4 (k + 1) ^ 2 + 3 (k + 1) + 12)` when `R` has width at most `k`, where
`n + 1` is the number of nodes.

## The program

The tables are indexed by bit masks over the ordered bags (`ofMask`, `toMask`). The nodes are
processed in the order `n, n - 1, …, 1`, so every child is processed before its parent. Processing
a node `j` with bag list `LB` and parent bag list `LP` (`processM`) runs two loops:

* the child pass (`childPassM`) visits each of the `2 ^ |LB|` child masks `t`. It tests whether
  the subset `T` selected by `t` is independent, computes the parent-bag mask of `T` and the weight
  of the vertices of `T` outside the parent bag, and updates the entry of a zero-initialized array
  `best` at that parent-bag mask with the maximum of its old value and the weight plus the table
  entry of `j` at `t`;
* the parent pass (`parentPassM`) visits each of the `2 ^ |LP|` parent masks `s`. It computes the
  parent-bag mask of `S ∩ B`, for the parent subset `S` selected by `s` and the child bag `B`, and
  adds the entry of `best` there to the parent's table entry at `s`.

The root pass (`rootPassM`) returns the best weight plus table entry over the independent subsets
of the root bag. `getD_tablesFPT` shows that the arrays agree with `tables` on every subset of
every bag. It is proved one node at a time against `step` (`getD_processM`). The only nontrivial
step is that the child pass computes `forget` (`getD_childPassM_eq_forget`).

## Cost model

The ticks count the operations of a unit-cost RAM with an adjacency matrix: an adjacency query
`G.Adj u v`, an equality test of vertices, a weight lookup `w v`, an array read or write, and
arithmetic and comparisons on masks and weights cost one unit each. Each tick pays for a constant
number of these operations. Every step of a scan of a bag list costs one tick, which covers its
equality test or adjacency query, its bit extraction and its accumulator update (`memM`,
`selMemM`, `noAdjM`, `keyM`, `restrictM`, `forgetWeightM`, `indepM`). Each child mask costs `4`
further ticks, for the two table reads, the addition, the comparison, the write and the loop
step. Each parent mask costs `3`, for the two reads, the addition, the append and the loop step,
and each root mask costs `3`, for the read, the addition, the comparison and the loop step. A
zero array of size `c` costs `c` ticks and the `n + 1` initial empty tables cost `n + 1`. The
bookkeeping of a node costs `3`, which treats the bag lengths and the powers `2 ^ |L i|` as
available in unit time, as when each bag is stored with its length. All loops are oblivious:
their iteration counts depend only on the bag sizes, so the tick count is the closed form
`time_mwisFPT`.

Membership is tested by linear scans of the bag lists rather than with precomputed index maps, so
a child mask costs `O(k ^ 2)` ticks rather than `O(k)`. The bound is still of the form
`2 ^ k · poly(k)` per node. The ticks model in-place updates of the arrays. The program uses its
arrays linearly: the scratch array `best` and the vector of tables are threaded through the
loops, and the tables of a node and of its parent are read before the parent's table is
replaced. So the compiled code can update them in place, and the compiled run at depth `2000` in
the tests is fast. This is not proved, and the ticks do not charge any copying of a shared array.

## Limitations

* The caller supplies the decomposition and the ordering `L` of its bags (`sortedBags` builds one
  for a linearly ordered vertex type). Computing a decomposition, ordering the bags and reading
  the input are not charged.
* The node count `n + 1` is a parameter of the decomposition and is not bounded in terms of
  `card V` here.
* There is no encoded instance and no `FPT` membership statement.

## Main definitions

* `Cslib.Algorithms.Lean.TreeDecomposition.mwisFPT`: the executable program.
* `Cslib.Algorithms.Lean.TreeDecomposition.fptNodeBound`: the per-node bound
  `2 ^ m (4 m ^ 2 + 3 m + 12)` for bags of at most `m` vertices.

## Main results

* `Cslib.Algorithms.Lean.TreeDecomposition.ret_mwisFPT`: the program returns `mwisValue R w`.
* `Cslib.Algorithms.Lean.TreeDecomposition.isGreatest_mwisFPT`: so it returns the maximum weight of
  an independent set.
* `Cslib.Algorithms.Lean.TreeDecomposition.time_mwisFPT`: its exact tick count.
* `Cslib.Algorithms.Lean.TreeDecomposition.time_mwisFPT_le`: at most
  `(n + 1) · fptNodeBound (k + 1)` ticks for width at most `k`.

## References

[CyganEtAl2015, Section 7.3.1] solves weighted independent set on an `n`-vertex graph, given a
tree decomposition of width at most `k`, in time `2 ^ k · k ^ O(1) · n`. There `n` is the number
of vertices: the given decomposition is first turned into a nice tree decomposition with
`O(k · n)` nodes, and the dynamic program over it spends `2 ^ k · k ^ O(1)` time per node. This
program instead uses the arbitrary rooted decompositions of
`CslibFrontier.Algorithms.Lean.TreeDecomposition.IndependentSet`: each nonroot node sends its parent
a
message indexed by the subsets of the parent's bag, and a parent adds the messages of its
children, so it needs no nice decomposition. It matches the per-node form `2 ^ k · k ^ O(1)` of
the source and is linear in the number `n + 1` of decomposition nodes. Relating that number to
the number of vertices, which the source's bound in `n` requires, is not done here.

* [M. Cygan et al., *Parameterized Algorithms*, Section 7.3.1][CyganEtAl2015]
-/

public section

namespace Cslib.Algorithms.Lean.TreeDecomposition

open SimpleGraph SimpleGraph.RootedTreeDecomposition

/-! ### The passes -/

section PassDefs

variable {V : Type*} [DecidableEq V]

/-- The parent pass: for each parent mask `s < c`, add the best child entry agreeing with `s` to
the old parent table. -/
@[expose] def parentPassM (LB LP : List V) (old best : Array ℕ) : ℕ → TimeM ℕ (Array ℕ)
  | 0 => pure #[]
  | c + 1 => do
    let acc ← parentPassM LB LP old best c
    let r ← restrictM LB LP c
    TimeM.tick 3
    pure (acc.push (old.getD c 0 + best.getD r 0))

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The child pass over the child masks `t < c`: for each independent child subset, update the
entry of `best` at its parent-bag mask with the forgotten weight plus the child table entry. -/
@[expose] def childPassM (w : V → ℕ) (LB LP : List V) (f init : Array ℕ) :
    ℕ → TimeM ℕ (Array ℕ)
  | 0 => pure init
  | c + 1 => do
    let best ← childPassM w LB LP f init c
    let ok ← indepM G LB c
    let key ← keyM LB LP c
    let fw ← forgetWeightM w LP LB c
    TimeM.tick 4
    pure (if ok then best.setIfInBounds key (max (best.getD key 0) (fw + f.getD c 0)) else best)

/-- The root pass over the root masks `t < c`: the best weight of an independent root subset plus
its table entry. -/
@[expose] def rootPassM (w : V → ℕ) (L : List V) (tbl : Array ℕ) : ℕ → TimeM ℕ ℕ
  | 0 => pure 0
  | c + 1 => do
    let best ← rootPassM w L tbl c
    let ok ← indepM G L c
    let sw ← forgetWeightM w [] L c
    TimeM.tick 3
    pure (if ok then max best (sw + tbl.getD c 0) else best)

end PassDefs

/-! ### The program -/

section Program

variable {V : Type*} {G : SimpleGraph V} {n : ℕ} [DecidableEq V] [DecidableRel G.Adj]

/-- Process node `j`: build its message to its parent and add it to the parent's table. -/
@[expose] def processM (R : G.RootedTreeDecomposition n) (w : V → ℕ)
    (L : Fin (n + 1) → List V) (st : Vector (Array ℕ) (n + 1)) (j : Fin (n + 1)) :
    TimeM ℕ (Vector (Array ℕ) (n + 1)) := do
  let p := R.parent j
  TimeM.tick 3
  let init ← zerosM (2 ^ (L p).length)
  let best ← childPassM G w (L j) (L p) st[j] init (2 ^ (L j).length)
  let tp ← parentPassM (L j) (L p) st[p] best (2 ^ (L p).length)
  pure (st.set p tp p.isLt)

/-- The tables after processing the nodes `n, n - 1, …, n - t + 1`. -/
@[expose] def tablesFPT (R : G.RootedTreeDecomposition n) (w : V → ℕ)
    (L : Fin (n + 1) → List V) : ℕ → TimeM ℕ (Vector (Array ℕ) (n + 1))
  | 0 => do
    TimeM.tick (n + 1)
    pure (Vector.replicate (n + 1) #[])
  | t + 1 => do
    let st ← tablesFPT R w L t
    processM R w L st (Fin.ofNat (n + 1) (n - t))

/-- The executable program: process every nonroot node, then combine at the root. -/
@[expose] def mwisFPT (R : G.RootedTreeDecomposition n) (w : V → ℕ)
    (L : Fin (n + 1) → List V) : TimeM ℕ ℕ := do
  let st ← tablesFPT R w L n
  rootPassM G w (L 0) st[(0 : Fin (n + 1))] (2 ^ (L 0).length)

end Program

/-! ### Correctness of the passes -/

section Passes

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem size_childPassM (w : V → ℕ) (LB LP : List V) (f init : Array ℕ) (c : ℕ) :
    (childPassM G w LB LP f init c).ret.size = init.size := by
  induction c with
  | zero => rfl
  | succ c ih =>
    simp only [childPassM, TimeM.ret_bind, TimeM.ret_pure]
    split_ifs
    · rw [Array.size_setIfInBounds, ih]
    · exact ih

/-- After the child masks `t < c`, the entry of `best` at a parent mask `k` is the best value over
the independent child subsets with parent mask `k`. -/
theorem getD_childPassM (w : V → ℕ) {LB : List V} (hLB : LB.Nodup) (LP : List V)
    (f init : Array ℕ) (c : ℕ) {k : ℕ} (hk : k < init.size) :
    (childPassM G w LB LP f init c).ret.getD k 0 = max (init.getD k 0)
      (((Finset.range c).filter fun t => G.IsIndepSet (↑(ofMask LB t) : Set V) ∧
          toMask LP (ofMask LB t) = k).sup fun t =>
        (∑ v ∈ ofMask LB t \ LP.toFinset, w v) + f.getD t 0) := by
  induction c with
  | zero => simp [childPassM]
  | succ c ih =>
    simp only [childPassM, TimeM.ret_bind, TimeM.ret_pure, ret_keyM,
      ret_forgetWeightM w LP hLB]
    rw [Finset.range_add_one, Finset.filter_insert]
    by_cases hok : (indepM G LB c).ret = true
    · have hind := (ret_indepM G LB c).1 hok
      rw [ite_eq_left hok]
      by_cases hkey : toMask LP (ofMask LB c) = k
      · rw [ite_eq_left ⟨hind, hkey⟩, Finset.sup_insert, hkey, Array.getD_eq_getD_getElem?,
          Array.getElem?_setIfInBounds, ite_eq_left rfl,
          ite_eq_left (by rw [size_childPassM]; exact hk), Option.getD_some, ih]
        omega
      · rw [ite_eq_right fun h => hkey h.2, Array.getD_eq_getD_getElem?,
          Array.getElem?_setIfInBounds,
          ite_eq_right hkey, ← Array.getD_eq_getD_getElem?, ih]
    · have hind : ¬G.IsIndepSet (↑(ofMask LB c) : Set V) := fun h => hok ((ret_indepM G LB c).2 h)
      rw [ite_eq_right hok, ite_eq_right fun h => hind h.1, ih]

/-- Started from a zero table, the child pass computes `forget` on every parent subset. -/
theorem getD_childPassM_eq_forget (w : V → ℕ) {LB LP : List V} (hLB : LB.Nodup) (f : Array ℕ)
    (g : Finset V → ℕ) (hfg : ∀ t < 2 ^ LB.length, f.getD t 0 = g (ofMask LB t)) {S : Finset V}
    (hS : S ⊆ LP.toFinset) :
    (childPassM G w LB LP f (Array.replicate (2 ^ LP.length) 0) (2 ^ LB.length)).ret.getD
        (toMask LP (S ∩ LB.toFinset)) 0 =
      forget G w LB.toFinset LP.toFinset g S := by
  rw [getD_childPassM G w hLB LP f _ _ (by rw [Array.size_replicate]; exact toMask_lt _ _)]
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate, ite_eq_left (toMask_lt _ _),
    Option.getD_some, Nat.zero_max]
  unfold forget
  rw [powerset_toFinset_eq_image, Finset.filter_image, Finset.sup_image]
  refine Finset.sup_congr ?_ fun t ht => ?_
  · refine Finset.filter_congr fun t _ => and_congr_right fun _ => ?_
    rw [toMask_eq_toMask_iff]
    constructor
    · intro h
      ext x
      have := congrArg (x ∈ ·) h
      simp only [Finset.mem_inter, eq_iff_iff] at this ⊢
      constructor
      · rintro ⟨hxt, hxP⟩
        exact ⟨(this.1 ⟨hxt, hxP⟩).1.1, (List.mem_toFinset.1 (ofMask_subset LB t hxt)) |>
          List.mem_toFinset.2⟩
      · rintro ⟨hxS, hxB⟩
        exact ⟨(this.2 ⟨⟨hxS, hxB⟩, hS hxS⟩).1, hS hxS⟩
    · intro h
      rw [h]
      exact (Finset.inter_eq_left.2 (Finset.inter_subset_left.trans hS)).symm
  · rw [Finset.mem_filter, Finset.mem_range] at ht
    simp only [Function.comp_apply, hfg t ht.1]

theorem size_parentPassM (LB LP : List V) (old best : Array ℕ) (c : ℕ) :
    (parentPassM LB LP old best c).ret.size = c := by
  induction c with
  | zero => rfl
  | succ c ih => simp [parentPassM, ih]

theorem getD_parentPassM (LB : List V) {LP : List V} (hLP : LP.Nodup) (old best : Array ℕ)
    {c s : ℕ} (hs : s < c) :
    (parentPassM LB LP old best c).ret.getD s 0 =
      old.getD s 0 + best.getD (toMask LP (ofMask LP s ∩ LB.toFinset)) 0 := by
  induction c with
  | zero => omega
  | succ c ih =>
    simp only [parentPassM, TimeM.ret_bind, TimeM.ret_pure, ret_restrictM LB hLP]
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_push, size_parentPassM]
    by_cases hsc : s = c
    · subst hsc
      rw [ite_eq_left rfl, Option.getD_some]
    · rw [ite_eq_right hsc, ← Array.getD_eq_getD_getElem?, ih (by omega)]

theorem ret_rootPassM (w : V → ℕ) {L : List V} (hL : L.Nodup) (tbl : Array ℕ) (c : ℕ) :
    (rootPassM G w L tbl c).ret =
      ((Finset.range c).filter fun t => G.IsIndepSet (↑(ofMask L t) : Set V)).sup fun t =>
        (∑ v ∈ ofMask L t, w v) + tbl.getD t 0 := by
  induction c with
  | zero => rfl
  | succ c ih =>
    simp only [rootPassM, TimeM.ret_bind, TimeM.ret_pure, ih, ret_forgetWeightM w [] hL,
      List.toFinset_nil, Finset.sdiff_empty]
    rw [Finset.range_add_one, Finset.filter_insert]
    by_cases hok : (indepM G L c).ret = true
    · rw [ite_eq_left hok, ite_eq_left ((ret_indepM G L c).1 hok), Finset.sup_insert]
      omega
    · rw [ite_eq_right hok, ite_eq_right fun h => hok ((ret_indepM G L c).2 h)]

end Passes

/-! ### Correctness -/

section Correctness

variable {V : Type*} {G : SimpleGraph V} {n : ℕ} [DecidableEq V] [DecidableRel G.Adj]

/-- One step of the program refines `step`: if the materialized tables agree with `g` on every
subset of every bag, then after processing `j` they agree with `step R w g j`. -/
theorem getD_processM (R : G.RootedTreeDecomposition n) (w : V → ℕ) {L : Fin (n + 1) → List V}
    (hL : IsBagOrder R L) (st : Vector (Array ℕ) (n + 1)) (g : Fin (n + 1) → Finset V → ℕ)
    (hg : ∀ i, ∀ s < 2 ^ (L i).length, st[i].getD s 0 = g i (ofMask (L i) s)) (j i : Fin (n + 1))
    {s : ℕ} (hs : s < 2 ^ (L i).length) :
    (processM R w L st j).ret[i].getD s 0 = step R w g j i (ofMask (L i) s) := by
  simp only [processM, TimeM.ret_bind, TimeM.ret_pure, ret_zerosM]
  unfold step
  by_cases hi : i = R.parent j
  · subst hi
    rw [Function.update_self, Fin.getElem_fin, Vector.getElem_set_self,
      getD_parentPassM _ (hL _).1 _ _ hs, hg _ _ hs,
      getD_childPassM_eq_forget G w (hL j).1 _ (g j) (hg j) (ofMask_subset _ _), (hL j).2,
      (hL (R.parent j)).2]
  · rw [Function.update_of_ne hi, Fin.getElem_fin,
      Vector.getElem_set_ne _ _ (fun h => hi (Fin.ext h).symm)]
    exact hg i s hs

/-- The materialized tables agree with the specification `tables` of
`CslibFrontier.Algorithms.Lean.TreeDecomposition.IndependentSet` on every subset of every bag. -/
theorem getD_tablesFPT (R : G.RootedTreeDecomposition n) (w : V → ℕ) {L : Fin (n + 1) → List V}
    (hL : IsBagOrder R L) (t : ℕ) (i : Fin (n + 1)) {s : ℕ} (hs : s < 2 ^ (L i).length) :
    (tablesFPT R w L t).ret[i].getD s 0 = tables R w t i (ofMask (L i) s) := by
  induction t generalizing i s with
  | zero => simp [tablesFPT, tables]
  | succ t ih =>
    simp only [tablesFPT, TimeM.ret_bind]
    exact getD_processM R w hL _ (tables R w t) (fun i s hs => ih i hs) _ i hs

/-- **Correctness.** The executable program returns the value of the dynamic program. -/
theorem ret_mwisFPT (R : G.RootedTreeDecomposition n) (w : V → ℕ) {L : Fin (n + 1) → List V}
    (hL : IsBagOrder R L) : (mwisFPT R w L).ret = mwisValue R w := by
  simp only [mwisFPT, TimeM.ret_bind]
  rw [ret_rootPassM G w (hL 0).1, mwisValue, ← (hL 0).2, powerset_toFinset_eq_image,
    Finset.filter_image, Finset.sup_image]
  refine Finset.sup_congr rfl fun t ht => ?_
  rw [Finset.mem_filter, Finset.mem_range] at ht
  simp only [Function.comp_apply, getD_tablesFPT R w hL n 0 ht.1]

/-- The executable program returns the maximum weight of an independent set. -/
theorem isGreatest_mwisFPT (R : G.RootedTreeDecomposition n) (w : V → ℕ)
    {L : Fin (n + 1) → List V} (hL : IsBagOrder R L) :
    IsGreatest {x | ∃ I : Finset V, G.IsIndepSet (↑I : Set V) ∧ ∑ v ∈ I, w v = x}
      (mwisFPT R w L).ret := by
  rw [ret_mwisFPT R w hL]
  exact isGreatest_mwisValue R w

/-- With unit weights the executable program returns the independence number. -/
theorem mwisFPT_one_eq_indepNum (R : G.RootedTreeDecomposition n) {L : Fin (n + 1) → List V}
    (hL : IsBagOrder R L) : (mwisFPT R (fun _ => 1) L).ret = G.indepNum := by
  rw [ret_mwisFPT R _ hL, mwisValue_one_eq_indepNum]

end Correctness

/-! ### Running time -/

section Time

/-- The ticks of processing a nonroot node with `b` bag vertices whose parent has `q` bag
vertices: `3` for the bookkeeping, `2 ^ q` to allocate `best`, then per child mask the independence
test, the parent-bag mask, the forgotten weight and `4`, and per parent mask the restriction and
`3`. -/
@[expose] def processTime (b q : ℕ) : ℕ :=
  3 + 2 ^ q + 2 ^ b * (indepCost b + q * (b + 1) + b * (q + 1) + 4) +
    2 ^ q * (q * (b + 1) + 3)

/-- The ticks of the root pass on a root bag with `r` vertices: per root mask the independence test,
the weight of the subset and `3`. -/
@[expose] def rootPassTime (r : ℕ) : ℕ :=
  2 ^ r * (indepCost r + r + 3)

/-- The per-node bound `2 ^ m (4 m ^ 2 + 3 m + 12)` for bags of at most `m` vertices. -/
@[expose] def fptNodeBound (m : ℕ) : ℕ :=
  2 ^ m * (4 * m ^ 2 + 3 * m + 12)

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem time_childPassM (w : V → ℕ) (LB LP : List V) (f init : Array ℕ) (c : ℕ) :
    (childPassM G w LB LP f init c).time = c * (indepCost LB.length +
      LP.length * (LB.length + 1) + LB.length * (LP.length + 1) + 4) := by
  induction c with
  | zero => simp [childPassM]
  | succ c ih =>
    simp only [childPassM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, ih, time_indepM,
      time_keyM, time_forgetWeightM]
    ring

omit [DecidableRel G.Adj] in
theorem time_parentPassM (LB LP : List V) (old best : Array ℕ) (c : ℕ) :
    (parentPassM LB LP old best c).time = c * (LP.length * (LB.length + 1) + 3) := by
  induction c with
  | zero => simp [parentPassM]
  | succ c ih =>
    simp only [parentPassM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, ih,
      time_restrictM]
    ring

theorem time_rootPassM (w : V → ℕ) (L : List V) (tbl : Array ℕ) (c : ℕ) :
    (rootPassM G w L tbl c).time = c * (indepCost L.length + L.length + 3) := by
  induction c with
  | zero => simp [rootPassM]
  | succ c ih =>
    simp only [rootPassM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, ih, time_indepM,
      time_forgetWeightM, List.length_nil]
    ring

variable {G} {n : ℕ}

theorem time_processM (R : G.RootedTreeDecomposition n) (w : V → ℕ) (L : Fin (n + 1) → List V)
    (st : Vector (Array ℕ) (n + 1)) (j : Fin (n + 1)) :
    (processM R w L st j).time = processTime (L j).length (L (R.parent j)).length := by
  simp only [processM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, time_zerosM,
    time_childPassM, time_parentPassM, processTime]
  ring

theorem time_tablesFPT (R : G.RootedTreeDecomposition n) (w : V → ℕ) (L : Fin (n + 1) → List V)
    (t : ℕ) : (tablesFPT R w L t).time = (n + 1) + ∑ s ∈ Finset.range t,
      processTime (L (Fin.ofNat (n + 1) (n - s))).length
        (L (R.parent (Fin.ofNat (n + 1) (n - s)))).length := by
  induction t with
  | zero => simp [tablesFPT]
  | succ t ih =>
    simp only [tablesFPT, TimeM.time_bind, ih, time_processM, Finset.sum_range_succ]
    ring

private theorem sum_range_ofNat_sub (g : Fin (n + 1) → ℕ) :
    ∑ s ∈ Finset.range n, g (Fin.ofNat (n + 1) (n - s)) = ∑ i : Fin n, g i.succ := by
  have h1 : ∑ i : Fin n, g i.succ = ∑ i : Fin n, g (Fin.ofNat (n + 1) (i + 1)) := by
    refine Finset.sum_congr rfl fun i _ => congrArg g (Fin.ext ?_)
    simp [Nat.mod_eq_of_lt (Nat.succ_lt_succ i.isLt)]
  rw [h1, Fin.sum_univ_eq_sum_range (fun i => g (Fin.ofNat (n + 1) (i + 1))) n,
    ← Finset.sum_range_reflect (fun i => g (Fin.ofNat (n + 1) (i + 1))) n]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [Finset.mem_range] at hs
  congr 2
  omega

/-- **Exact running time.** The program charges `n + 1` ticks to allocate the tables, then
`processTime b q` per nonroot node with bag size `b` and parent bag size `q`, and
`rootPassTime r` at a root bag of size `r`. -/
theorem time_mwisFPT (R : G.RootedTreeDecomposition n) (w : V → ℕ) (L : Fin (n + 1) → List V) :
    (mwisFPT R w L).time = (n + 1) + (∑ i : Fin n,
      processTime (L i.succ).length (L (R.parent i.succ)).length) + rootPassTime (L 0).length := by
  simp only [mwisFPT, TimeM.time_bind, time_tablesFPT, time_rootPassM, rootPassTime,
    sum_range_ofNat_sub (fun i => processTime (L i).length (L (R.parent i)).length)]

theorem processTime_mono {b b' q q' : ℕ} (hb : b ≤ b') (hq : q ≤ q') :
    processTime b q ≤ processTime b' q' := by
  unfold processTime
  have h1 : 2 ^ b ≤ 2 ^ b' := Nat.pow_le_pow_right (by norm_num) hb
  have h2 : 2 ^ q ≤ 2 ^ q' := Nat.pow_le_pow_right (by norm_num) hq
  have h3 := indepCost_mono hb
  gcongr

theorem rootPassTime_mono {r r' : ℕ} (hr : r ≤ r') : rootPassTime r ≤ rootPassTime r' := by
  unfold rootPassTime
  have h1 : 2 ^ r ≤ 2 ^ r' := Nat.pow_le_pow_right (by norm_num) hr
  have h3 := indepCost_mono hr
  gcongr

theorem processTime_add_one_le (m : ℕ) : processTime m m + 1 ≤ fptNodeBound m := by
  unfold processTime fptNodeBound
  have hI := indepCost_le m
  have hP : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have hPI : 2 ^ m * indepCost m ≤ 2 ^ m * (m * m) := Nat.mul_le_mul_left _ hI
  nlinarith

theorem rootPassTime_add_one_le (m : ℕ) : rootPassTime m + 1 ≤ fptNodeBound m := by
  unfold rootPassTime fptNodeBound
  have hI := indepCost_le m
  have hP : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have hPI : 2 ^ m * indepCost m ≤ 2 ^ m * (m * m) := Nat.mul_le_mul_left _ hI
  nlinarith

/-- **FPT running time.** On a rooted decomposition with `n + 1` nodes (decomposition nodes, not
vertices of `G`) and width at most `k`, the program takes at most
`(n + 1) · 2 ^ (k + 1) · (4 (k + 1) ^ 2 + 3 (k + 1) + 12)` ticks: linear in the number of nodes and
`2 ^ k · poly(k)` per node. This is the per-node form of [CyganEtAl2015, Section 7.3.1]; the
source's bound is linear in the number of vertices, and the node count `n + 1` is not bounded in
terms of `card V` here. -/
theorem time_mwisFPT_le (R : G.RootedTreeDecomposition n) (w : V → ℕ) {L : Fin (n + 1) → List V}
    (hL : IsBagOrder R L) {k : ℕ} (hk : R.width ≤ k) :
    (mwisFPT R w L).time ≤ (n + 1) * fptNodeBound (k + 1) := by
  have hlen : ∀ i, (L i).length ≤ k + 1 := fun i => by
    rw [← List.toFinset_card_of_nodup (hL i).1, (hL i).2]
    exact R.width_le_iff.1 hk i
  have hnode : ∀ i : Fin n,
      processTime (L i.succ).length (L (R.parent i.succ)).length + 1 ≤ fptNodeBound (k + 1) :=
    fun i => (Nat.add_le_add_right (processTime_mono (hlen _) (hlen _)) 1).trans
      (processTime_add_one_le _)
  have hsum : ∑ i : Fin n, (processTime (L i.succ).length (L (R.parent i.succ)).length + 1) ≤
      n * fptNodeBound (k + 1) := by
    simpa using Finset.sum_le_card_nsmul Finset.univ _ _ fun i _ => hnode i
  have hroot := (Nat.add_le_add_right (rootPassTime_mono (hlen 0)) 1).trans
    (rootPassTime_add_one_le (k + 1))
  rw [time_mwisFPT, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one] at *
  nlinarith

end Time

end Cslib.Algorithms.Lean.TreeDecomposition
