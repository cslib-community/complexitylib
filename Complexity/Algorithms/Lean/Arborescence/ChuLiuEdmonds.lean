/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.Combinatorics.Digraph.Arborescence
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Data.FinEnum
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.List.MinMax
public import Mathlib.Dynamics.PeriodicPts.Defs
import Complexity.Foundations.Combinatorics.FunctionalGraph
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Minimum-cost arborescences: the Chu–Liu/Edmonds algorithm

Given a finite digraph `G` with decidable arcs, arc costs `c : V → V → β` in a linearly ordered
additive commutative monoid (for example `ℕ`, `ℤ` or `ℚ`; negative costs are allowed), and a root
`r`, the algorithm `Cslib.Algorithms.Lean.Arborescence.edmonds` returns a spanning in-arborescence
of `G` rooted at `r` of minimum total arc cost, or `none` if `G` has no spanning in-arborescence
rooted at `r` ([ChuLiu1965], [Edmonds1967Branchings]).

An in-arborescence is represented by its parent function `p : V → V`: `p r = r`, `v → p v` is an arc
of `G` for `v ≠ r`, and every vertex reaches `r` by iterating `p`
(`Cslib.Algorithms.Lean.Arborescence.IsInArborescenceParent`). Its cost is
`∑ v ≠ r, c v (p v)`. Parent functions correspond exactly to the spanning in-arborescences
`T ≤ G` of `Digraph.IsInArborescence` (`isInArborescenceParent_iff`, built on the parent-function
API `Digraph.parentDigraph` of `Complexity.Foundations.Combinatorics.Digraph.Arborescence`), and
`edmonds_optimal` states optimality directly over those digraphs. Out-arborescences (arcs
directed away from the root, Edmonds' convention) are handled by reversing the arcs
(`edmondsOut_spec`).

## The algorithm

Every non-root vertex selects a cheapest arc `v → cheapestParent v` to another vertex. If the
selection has no cycle, it is an arborescence, and it is optimal because each vertex pays the least
it can. Otherwise, take a cycle `C` of the selection and contract it onto one of its vertices `x0`,
keeping the vertex type:

* an arc `u → x0` from `u ∉ C` stands for the cheapest arc from `u` into `C` (`bestEntry`);
* an arc `x0 → w` to `w ∉ C` stands for the cheapest way to leave `C` towards `w`: an arc `x → w`
  with `x ∈ C`, plus the selected arcs of the other vertices of `C` (`bestExit`, `exitCost`);
* the other vertices of `C` keep only an arc of cost `0` to the root.

Then the contracted instance is solved recursively and the result expanded (`expandParent`): the
vertex of `C` that attains the exit leaves `C`, the other vertices of `C` keep their selected arcs,
and an arc into `x0` becomes the cheapest arc into `C`. Expansion preserves cost exactly
(`expandParent_spec`). Conversely, every arborescence of the original instance contracts to one of
the contracted instance of at most the same cost (`exists_contract_le`), the exchange argument: the
vertex of `C` closest to the root keeps its arc out of `C`, and the other vertices of `C` gain
nothing over their selected arcs. Hence an optimal solution of the contracted instance expands to an
optimal solution of the original one.

The contracted cost of leaving the cycle includes the selected costs of the other cycle vertices,
rather than subtracting the selected cost of the leaving vertex as in the usual presentation with
reduced costs. This is the same up to a constant, and needs no subtraction, so the costs may lie in
an ordered monoid such as `ℕ`. Contraction strictly shrinks the set of vertices with an arc to a
vertex other than themselves and the root, so `|V|` levels of recursion suffice (`edmonds` runs
`edmondsAux` with fuel `FinEnum.card V`).

## Main definitions

* `Cslib.Algorithms.Lean.Arborescence.IsInArborescenceParent`: parent functions of spanning
  in-arborescences.
* `Cslib.Algorithms.Lean.Arborescence.parentCost`: the cost of a parent function.
* `Cslib.Algorithms.Lean.Arborescence.arcCost`: the arc cost of a digraph, to state optimality over
  `Digraph.IsInArborescence` (with `Digraph.parentDigraph`, the digraph of a parent function).
* `Cslib.Algorithms.Lean.Arborescence.edmonds`: the Chu–Liu/Edmonds algorithm.
* `Cslib.Algorithms.Lean.Arborescence.edmondsOut`: the same for out-arborescences.

## Main results

* `Cslib.Algorithms.Lean.Arborescence.edmonds_spec`: if `edmonds G c r = some p`, then `p` is a
  spanning in-arborescence of `G` rooted at `r` of minimum cost; if it is `none`, there is none.
* `Cslib.Algorithms.Lean.Arborescence.edmonds_eq_none_iff`: `edmonds G c r = none` iff `G` has no
  spanning in-arborescence rooted at `r`.
* `Cslib.Algorithms.Lean.Arborescence.edmonds_optimal`: optimality over all spanning
  in-arborescences `T ≤ G` (`Digraph.IsInArborescence`), measured by their arc cost `arcCost`.
* `Cslib.Algorithms.Lean.Arborescence.edmondsOut_spec`: the out-arborescence form.
* `Cslib.Algorithms.Lean.Arborescence.expandParent_spec`,
  `Cslib.Algorithms.Lean.Arborescence.exists_contract_le`: the contraction lemmas.

## Source mapping

[Edmonds1967Branchings] treats spanning arborescences with arcs directed away from a prescribed
root, maximum or minimum weight, real weights. Section 2 reduces optimum spanning arborescences to
optimum branchings. Theorem 1, stated in Section 3, asserts a *good* (polynomially bounded)
algorithm for optimum branchings; Section 4 gives the algorithm, which selects the best arc into
each node and contracts cycles, and its proof. This module proves correctness and optimality of
that cycle-contraction algorithm, specialised to rooted minimum-cost spanning arborescences. It
does not prove the polynomial-time content of Theorem 1 (see Limitations). [ChuLiu1965] gives the
same contraction algorithm for shortest arborescences (not inspected here). [Schrijver2003],
Section 52.1 ("Finding a shortest r-arborescence"), is a textbook locator (from the table of
contents; not inspected). The theorems here are for in-arborescences, with costs in any linearly
ordered additive commutative monoid; `edmondsOut_spec` is Edmonds' orientation.

## Limitations

`edmonds` is executable but not efficient, and no running-time bound is proved. Each level of the
recursion receives the contracted arcs and costs as closures over those of the previous level,
without memoisation, so evaluating one contracted arc or cost re-evaluates the previous level many
times, and the worst-case running time is exponential in the number of nested contractions. A
polynomial version, such as the `O(n m)` bound, needs materialised per-level arc and cost tables;
Tarjan's `O(m log n)` and the Gabow–Galil–Spencer–Tarjan `O(m + n log n)` implementations are not
formalized either. Optimum
branchings (forests of maximum weight, Edmonds' Theorem 1 itself) and the branching polytope
(Edmonds' Theorem 2) are not treated.

## References

* [ChuLiu1965]
* [Edmonds1967Branchings]
* [Schrijver2003]
-/

public section

namespace Cslib.Algorithms.Lean.Arborescence

variable {V : Type*} {β : Type*}

/-! ### Parent functions of arborescences -/

/-- `p` is the parent function of a spanning in-arborescence rooted at `r` in the relation `R`:
the root is fixed, every other vertex has an arc `v → p v`, and every vertex reaches `r` by
iterating `p`. -/
structure IsInArborescenceParent (R : V → V → Prop) (r : V) (p : V → V) : Prop where
  /-- The root is its own parent. -/
  root : p r = r
  /-- Every other vertex has an arc to its parent. -/
  adj : ∀ v, v ≠ r → R v (p v)
  /-- Every vertex reaches the root. -/
  reach : ∀ v, ∃ n, p^[n] v = r

/-- In an arborescence no vertex other than the root is its own parent. -/
theorem IsInArborescenceParent.ne {R : V → V → Prop} {r : V} {p : V → V}
    (h : IsInArborescenceParent R r p) {v : V} (hv : v ≠ r) : p v ≠ v := by
  intro hpv
  obtain ⟨n, hn⟩ := h.reach v
  rw [Function.iterate_fixed hpv] at hn
  exact hv hn

/-- The cost `∑ v ≠ r, c v (p v)` of the arcs `v → p v` of a parent function. -/
@[expose] def parentCost [Fintype V] [DecidableEq V] [AddCommMonoid β] (c : V → V → β) (r : V)
    (p : V → V) : β :=
  ∑ v ∈ Finset.univ.erase r, c v (p v)

/-! ### Correspondence with `Digraph.IsInArborescence` -/

section Bridge

open Digraph

/-- Parent functions of spanning in-arborescences of `G` are exactly the parent functions whose
digraph is a spanning in-arborescence (`Digraph.IsInArborescence`) contained in `G`. -/
theorem isInArborescenceParent_iff {G : Digraph V} {r : V} {p : V → V} (hr : p r = r) :
    IsInArborescenceParent G.Adj r p ↔
      (parentDigraph r p).IsInArborescence r ∧ parentDigraph r p ≤ G := by
  rw [isInArborescence_parentDigraph_iff]
  exact ⟨fun h => ⟨h.reach, fun v w hvw => hvw.2 ▸ h.adj v hvw.1⟩,
    fun h => ⟨hr, fun v hv => h.2 ⟨hv, rfl⟩, h.1⟩⟩

/-- The arc cost `∑_{v → w ∈ T} c v w` of a digraph. -/
def arcCost [Fintype V] [AddCommMonoid β] (T : Digraph V) [DecidableRel T.Adj]
    (c : V → V → β) : β :=
  ∑ e ∈ Finset.univ.filter (fun e : V × V => T.Adj e.1 e.2), c e.1 e.2

/-- The arc cost of the digraph of a parent function is its cost. -/
theorem arcCost_parentDigraph [Fintype V] [DecidableEq V] [AddCommMonoid β] (r : V) (p : V → V)
    (c : V → V → β) : arcCost (Digraph.parentDigraph r p) c = parentCost c r p := by
  unfold arcCost parentCost
  have himg : (Finset.univ.erase r).image (fun v => (v, p v)) =
      Finset.univ.filter (fun e : V × V => (Digraph.parentDigraph r p).Adj e.1 e.2) := by
    ext ⟨v, w⟩
    simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true,
      Finset.mem_filter, true_and, Digraph.parentDigraph_adj, Prod.mk.injEq]
    constructor
    · rintro ⟨u, hu, rfl, rfl⟩
      exact ⟨hu, rfl⟩
    · rintro ⟨hv, rfl⟩
      exact ⟨v, hv, rfl, rfl⟩
  rw [← himg, Finset.sum_image fun x _ y _ h => (Prod.mk.inj h).1]

end Bridge

/-! ### Cheapest arcs -/

section Select

variable [FinEnum V] [LinearOrder β] (a : V → V → Bool) (c : V → V → β) (r : V)

/-- The possible parents of `v`: the vertices `w ≠ v` with an arc `v → w`. -/
@[expose] def candidates (v : V) : List V :=
  (FinEnum.toList V).filter fun w => a v w && w != v

omit [LinearOrder β] in
theorem mem_candidates {v w : V} : w ∈ candidates a v ↔ a v w = true ∧ w ≠ v := by
  simp [candidates, FinEnum.mem_toList]

/-- The root, for `r`; otherwise a cheapest candidate parent (or `v` itself if there is none). -/
@[expose] def cheapestParent (v : V) : V :=
  if v = r then r else (List.argmin (c v) (candidates a v)).getD v

theorem cheapestParent_root : cheapestParent a c r r = r := by simp [cheapestParent]

theorem cheapestParent_spec {v : V} (hv : v ≠ r) (hne : candidates a v ≠ []) :
    a v (cheapestParent a c r v) = true ∧ cheapestParent a c r v ≠ v ∧
      ∀ w, a v w = true → w ≠ v → c v (cheapestParent a c r v) ≤ c v w := by
  obtain ⟨m, hm⟩ := Option.ne_none_iff_exists'.mp (mt (List.argmin_eq_none (f := c v)).mp hne)
  have hsel : cheapestParent a c r v = m := by simp [cheapestParent, hv, hm]
  rw [hsel]
  have hmem := (mem_candidates a).mp (List.argmin_mem hm)
  exact ⟨hmem.1, hmem.2, fun w hw hwv =>
    List.le_of_mem_argmin ((mem_candidates a).mpr ⟨hw, hwv⟩) hm⟩

end Select

/-! ### Cycles of the selection -/

section Cycle

variable [FinEnum V] (r : V)

/-- A vertex other than `r` on a cycle of `f`, if there is one. -/
@[expose] def findCycle (f : V → V) : Option V :=
  (FinEnum.toList V).find? fun x =>
    x != r && (List.range (FinEnum.card V)).any fun k => f^[k + 1] x == x

private theorem findCycle_some {f : V → V} {x : V} (h : findCycle r f = some x) :
    x ≠ r ∧ ∃ k < FinEnum.card V, f^[k + 1] x = x := by
  have := List.find?_some h
  simpa [List.any_eq_true] using this

private theorem findCycle_none {f : V → V} (h : findCycle r f = none) {x : V} (hx : x ≠ r) {k : ℕ}
    (hk : k < FinEnum.card V) : f^[k + 1] x ≠ x := by
  have := List.find?_eq_none.mp h x (FinEnum.mem_toList x)
  simp only [bne_iff_ne, ne_eq, List.any_eq_true, List.mem_range, beq_iff_eq,
    Bool.and_eq_true, not_and, not_exists] at this
  exact this hx k hk

/-- If `f` has no cycle avoiding `r`, then every vertex reaches `r` by iterating `f`. -/
theorem reach_of_findCycle_none {f : V → V} (h : findCycle r f = none) (v : V) :
    ∃ n, f^[n] v = r := by
  obtain ⟨n, hn⟩ := Cslib.FunctionalGraph.exists_iterate_mem_periodicPts f v
  refine ⟨n, ?_⟩
  by_contra hy
  have hpos := Function.minimalPeriod_pos_of_mem_periodicPts hn
  have hle : Function.minimalPeriod f (f^[n] v) ≤ FinEnum.card V := by
    rw [FinEnum.card_eq_fintypeCard]
    exact Function.minimalPeriod_le_card
  apply findCycle_none r h hy (k := Function.minimalPeriod f (f^[n] v) - 1) (by omega)
  rw [Nat.sub_add_cancel hpos]
  exact Function.isPeriodicPt_minimalPeriod f _

/-- The orbit of `x0` under `f`; the cycle through `x0` when `x0` is periodic. -/
@[expose] def cycleOf (f : V → V) (x0 : V) : Finset V :=
  (Finset.range (FinEnum.card V)).image fun k => f^[k] x0

omit r in
theorem mem_cycleOf {f : V → V} {x0 y : V} :
    y ∈ cycleOf f x0 ↔ ∃ n < FinEnum.card V, f^[n] x0 = y := by
  simp [cycleOf]

variable {f : V → V} {x0 : V} {m : ℕ}

omit r in
theorem iterate_mem_cycleOf (hm : Function.IsPeriodicPt f m x0) (hm0 : 0 < m)
    (hmc : m ≤ FinEnum.card V) (n : ℕ) : f^[n] x0 ∈ cycleOf f x0 := by
  rw [← hm.iterate_mod_apply]
  exact mem_cycleOf.mpr ⟨n % m, lt_of_lt_of_le (Nat.mod_lt _ hm0) hmc, rfl⟩

omit r in
theorem map_mem_cycleOf (hm : Function.IsPeriodicPt f m x0) (hm0 : 0 < m)
    (hmc : m ≤ FinEnum.card V) {y : V} (hy : y ∈ cycleOf f x0) : f y ∈ cycleOf f x0 := by
  obtain ⟨n, -, rfl⟩ := mem_cycleOf.mp hy
  rw [← Function.iterate_succ_apply' f n x0]
  exact iterate_mem_cycleOf hm hm0 hmc _

omit r in
/-- On a cycle, every vertex reaches every other one. -/
theorem cycleOf_reach (hm : Function.IsPeriodicPt f m x0) (hm0 : 0 < m) {y z : V}
    (hy : y ∈ cycleOf f x0) (hz : z ∈ cycleOf f x0) : ∃ n, f^[n] y = z := by
  obtain ⟨i, -, rfl⟩ := mem_cycleOf.mp hy
  obtain ⟨j, -, rfl⟩ := mem_cycleOf.mp hz
  have hi : i ≤ j + m * i := le_add_left (Nat.le_mul_of_pos_left i hm0)
  refine ⟨j + m * i - i, ?_⟩
  rw [← Function.iterate_add_apply, Nat.sub_add_cancel hi, Function.iterate_add_apply,
    (hm.mul_const i).eq]

theorem root_notMem_cycleOf (hr : f r = r) (hx0 : x0 ≠ r) (hm : Function.IsPeriodicPt f m x0)
    (hm0 : 0 < m) (hmc : m ≤ FinEnum.card V) : r ∉ cycleOf f x0 := by
  intro h
  obtain ⟨N, hN⟩ := cycleOf_reach hm hm0 h (iterate_mem_cycleOf hm hm0 hmc 0)
  rw [Function.iterate_fixed hr] at hN
  exact hx0 hN.symm

end Cycle

/-- If `p` agrees with `f` on a set containing the first `n` iterates of `y` under `f`, then
`p^[n] y = f^[n] y`. -/
private theorem iterate_eq_of_agree {f p : V → V} {S : Set V} (hfp : ∀ y ∈ S, p y = f y)
    {y : V} : ∀ n, (∀ i < n, f^[i] y ∈ S) → p^[n] y = f^[n] y
  | 0, _ => rfl
  | n + 1, h => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      iterate_eq_of_agree hfp n (fun i hi => h i (by omega)), hfp _ (h n (by omega))]

/-! ### Contraction and expansion -/

section Contract

variable [FinEnum V] [LinearOrder β] [AddCommMonoid β]
variable (a : V → V → Bool) (c : V → V → β) (f : V → V) (C : Finset V) (x0 r : V)

/-- The cost of leaving `C` from `x` along `x → w`, plus the selected arcs `y → f y` of the other
vertices of `C`. -/
@[expose] def exitCost (x w : V) : β := c x w + ∑ y ∈ C.erase x, c y (f y)

/-- A vertex of `C` with an arc to `w` of least exit cost, if any. -/
@[expose] def bestExit (w : V) : Option V :=
  List.argmin (fun x => exitCost c f C x w)
    ((FinEnum.toList V).filter fun x => decide (x ∈ C) && a x w)

/-- A cheapest arc from `u` into `C`, by its head, if any. -/
@[expose] def bestEntry (u : V) : Option V :=
  List.argmin (c u) ((FinEnum.toList V).filter fun y => decide (y ∈ C) && a u y)

/-- The arcs after contracting `C` onto `x0`: `x0` has an arc to `w ∉ C` if some vertex of `C`
has, `u ∉ C` has an arc to `x0` if it has one into `C`, the other vertices of `C` have only an arc
to `r`, and arcs outside `C` are unchanged. -/
@[expose] def contractAdj (u w : V) : Bool :=
  if u ∈ C then
    if u = x0 then decide (w ∉ C) && (FinEnum.toList V).any fun x => decide (x ∈ C) && a x w
    else decide (w = r)
  else
    if w ∈ C then decide (w = x0) && (FinEnum.toList V).any fun y => decide (y ∈ C) && a u y
    else a u w

/-- The arc costs after contracting `C` onto `x0`: leaving `x0` costs the best exit cost,
entering `x0` costs the cheapest arc into `C`, the other vertices of `C` pay `0`, and arcs outside
`C` keep their costs. -/
@[expose] def contractCost (u w : V) : β :=
  if u ∈ C then
    if u = x0 then
      match bestExit a c f C w with
      | some x => exitCost c f C x w
      | none => c u w
    else 0
  else
    if w = x0 then
      match bestEntry a c C u with
      | some y => c u y
      | none => c u w
    else c u w

/-- Expand a parent function `q` of the contracted instance: the vertex of `C` attaining the best
exit towards `q x0` takes that arc, the other vertices of `C` keep `f`, and an arc into `x0`
becomes the cheapest arc into `C`. -/
@[expose] def expandParent (q : V → V) (v : V) : V :=
  if v ∈ C then
    match bestExit a c f C (q x0) with
    | some x => if v = x then q x0 else f v
    | none => f v
  else if q v = x0 then (bestEntry a c C v).getD v
  else q v

variable {a c f C x0 r}

omit [AddCommMonoid β] [LinearOrder β] in
private theorem contractAdj_rep_iff (hx0 : x0 ∈ C) {w : V} :
    contractAdj a C x0 r x0 w = true ↔ w ∉ C ∧ ∃ x ∈ C, a x w = true := by
  simp [contractAdj, hx0, List.any_eq_true, FinEnum.mem_toList]

omit [AddCommMonoid β] [LinearOrder β] in
private theorem contractAdj_mem_iff {u w : V} (hu : u ∈ C) (hux : u ≠ x0) :
    contractAdj a C x0 r u w = true ↔ w = r := by
  simp [contractAdj, hu, hux]

omit [AddCommMonoid β] [LinearOrder β] in
private theorem contractAdj_out_mem_iff {u w : V} (hu : u ∉ C) (hw : w ∈ C) :
    contractAdj a C x0 r u w = true ↔ w = x0 ∧ ∃ y ∈ C, a u y = true := by
  simp [contractAdj, hu, hw, List.any_eq_true, FinEnum.mem_toList]

omit [AddCommMonoid β] [LinearOrder β] in
private theorem contractAdj_out_out_iff {u w : V} (hu : u ∉ C) (hw : w ∉ C) :
    contractAdj a C x0 r u w = true ↔ a u w = true := by
  simp [contractAdj, hu, hw]

private theorem bestExit_spec {w : V} (h : ∃ x ∈ C, a x w = true) :
    ∃ x, bestExit a c f C w = some x ∧ x ∈ C ∧ a x w = true ∧
      ∀ y ∈ C, a y w = true → exitCost c f C x w ≤ exitCost c f C y w := by
  obtain ⟨y, hy, hyw⟩ := h
  have hmem : y ∈ (FinEnum.toList V).filter (fun x => decide (x ∈ C) && a x w) := by
    simp [FinEnum.mem_toList, hy, hyw]
  obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp
    (mt (List.argmin_eq_none (f := fun x => exitCost c f C x w)).mp (List.ne_nil_of_mem hmem))
  have hxm := List.argmin_mem hx
  simp only [List.mem_filter, FinEnum.mem_toList, true_and, Bool.and_eq_true,
    decide_eq_true_eq] at hxm
  exact ⟨x, hx, hxm.1, hxm.2, fun z hz hzw =>
    List.le_of_mem_argmin (by simp [FinEnum.mem_toList, hz, hzw]) hx⟩

omit [AddCommMonoid β] in
private theorem bestEntry_spec {u : V} (h : ∃ y ∈ C, a u y = true) :
    ∃ y, bestEntry a c C u = some y ∧ y ∈ C ∧ a u y = true ∧
      ∀ z ∈ C, a u z = true → c u y ≤ c u z := by
  obtain ⟨y, hy, hyw⟩ := h
  have hmem : y ∈ (FinEnum.toList V).filter (fun z => decide (z ∈ C) && a u z) := by
    simp [FinEnum.mem_toList, hy, hyw]
  obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp
    (mt (List.argmin_eq_none (f := c u)).mp (List.ne_nil_of_mem hmem))
  have hxm := List.argmin_mem hx
  simp only [List.mem_filter, FinEnum.mem_toList, true_and, Bool.and_eq_true,
    decide_eq_true_eq] at hxm
  exact ⟨x, hx, hxm.1, hxm.2, fun z hz hzw =>
    List.le_of_mem_argmin (by simp [FinEnum.mem_toList, hz, hzw]) hx⟩

/-- **Expansion.** If `C` is a cycle of `f` avoiding `r`, along arcs of `a`, then every
arborescence `q` of the contracted instance expands to an arborescence of the original instance
of the same cost. -/
theorem expandParent_spec (hfa : ∀ y ∈ C, a y (f y) = true) (hfC : ∀ y ∈ C, f y ∈ C)
    (hx0 : x0 ∈ C) (hrC : r ∉ C) (hreach : ∀ y ∈ C, ∀ z ∈ C, ∃ n, f^[n] y = z) {q : V → V}
    (hq : IsInArborescenceParent (fun u w => contractAdj a C x0 r u w = true) r q) :
    IsInArborescenceParent (fun u w => a u w = true) r (expandParent a c f C x0 q) ∧
      parentCost c r (expandParent a c f C x0 q) = parentCost (contractCost a c f C x0) r q := by
  have hx0r : x0 ≠ r := fun h => hrC (h ▸ hx0)
  obtain ⟨hwC, hex⟩ := (contractAdj_rep_iff hx0).mp (hq.adj x0 hx0r)
  obtain ⟨xs, hbo, hxsC, hxsa, -⟩ := bestExit_spec (c := c) (f := f) hex
  have hpC : ∀ v ∈ C, expandParent a c f C x0 q v = if v = xs then q x0 else f v := by
    intro v hv
    simp [expandParent, hv, hbo]
  have hqO : ∀ v ∉ C, q v ≠ x0 → q v ∉ C := by
    intro v hv hqv hqC
    have hvr : v ≠ r := by
      rintro rfl
      exact hrC (hq.root ▸ hqC)
    exact hqv ((contractAdj_out_mem_iff hv hqC).mp (hq.adj v hvr)).1
  have hpO : ∀ v ∉ C, q v = x0 → ∃ y, y ∈ C ∧ a v y = true ∧ bestEntry a c C v = some y ∧
      expandParent a c f C x0 q v = y := by
    intro v hv hqv
    have hvr : v ≠ r := by
      rintro rfl
      exact hx0r (hqv ▸ hq.root)
    have h1 := hq.adj v hvr
    rw [hqv] at h1
    have h := (contractAdj_out_mem_iff hv hx0).mp h1
    obtain ⟨y, hbi, hyC, hya, -⟩ := bestEntry_spec (c := c) h.2
    exact ⟨y, hyC, hya, hbi, by simp [expandParent, hv, hqv, hbi]⟩
  have hpO' : ∀ v ∉ C, q v ≠ x0 → expandParent a c f C x0 q v = q v := by
    intro v hv hqv
    simp [expandParent, hv, hqv]
  set p := expandParent a c f C x0 q with hp
  -- every vertex of `C` reaches `q x0`
  have hR1 : ∀ y ∈ C, ∃ n, p^[n] y = q x0 := by
    intro y hy
    have hex : ∃ n, f^[n] y = xs := hreach y hy xs hxsC
    classical
    have hiC : ∀ i, f^[i] y ∈ C := fun i => Set.MapsTo.iterate (s := (C : Set V)) hfC i hy
    refine ⟨Nat.find hex + 1, ?_⟩
    rw [Function.iterate_succ_apply', iterate_eq_of_agree (S := {z | z ∈ C ∧ z ≠ xs})
      (fun z hz => by rw [hpC z hz.1, ite_eq_right hz.2]) _
      (fun i hi => ⟨hiC i, Nat.find_min hex hi⟩), Nat.find_spec hex, hpC xs hxsC,
      ite_eq_left rfl]
  -- vertices outside `C` that reach `r` under `q` reach it under `p`
  have hR2 : ∀ n u, u ∉ C → q^[n] u = r → ∃ m, p^[m] u = r := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro u hu hn
      by_cases hur : u = r
      · exact ⟨0, hur⟩
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := by
        rcases n with _ | n'
        · exact absurd hn hur
        · exact ⟨n', rfl⟩
      rw [Function.iterate_succ_apply] at hn
      by_cases hqu : q u = x0
      · rw [hqu] at hn
        obtain ⟨n'', rfl⟩ : ∃ n'', n' = n'' + 1 := by
          rcases n' with _ | n''
          · exact absurd hn hx0r
          · exact ⟨n'', rfl⟩
        rw [Function.iterate_succ_apply] at hn
        obtain ⟨m, hm⟩ := ih n'' (by omega) (q x0) hwC hn
        obtain ⟨y, hyC, -, -, hpy⟩ := hpO u hu hqu
        obtain ⟨k, hk⟩ := hR1 y hyC
        refine ⟨m + k + 1, ?_⟩
        rw [Function.iterate_succ_apply, hpy, Function.iterate_add_apply, hk, hm]
      · obtain ⟨m, hm⟩ := ih n' (by omega) (q u) (hqO u hu hqu) hn
        exact ⟨m + 1, by rw [Function.iterate_succ_apply, hpO' u hu hqu, hm]⟩
  have hrx0 : q r ≠ x0 := by rw [hq.root]; exact hx0r.symm
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hpO' r hrC hrx0, hq.root]
  · intro v hv
    by_cases hvC : v ∈ C
    · rw [hpC v hvC]
      split_ifs with hvx
      · subst hvx; exact hxsa
      · exact hfa v hvC
    · by_cases hqv : q v = x0
      · obtain ⟨y, -, hya, -, hpy⟩ := hpO v hvC hqv
        rw [hpy]; exact hya
      · rw [hpO' v hvC hqv]
        exact (contractAdj_out_out_iff hvC (hqO v hvC hqv)).mp (hq.adj v hv)
  · intro v
    by_cases hvC : v ∈ C
    · obtain ⟨k, hk⟩ := hR1 v hvC
      obtain ⟨n, hn⟩ := hq.reach (q x0)
      obtain ⟨m, hm⟩ := hR2 n (q x0) hwC hn
      exact ⟨m + k, by rw [Function.iterate_add_apply, hk, hm]⟩
    · obtain ⟨n, hn⟩ := hq.reach v
      exact hR2 n v hvC hn
  · have hsub : C ⊆ Finset.univ.erase r := fun y hy =>
      Finset.mem_erase.mpr ⟨fun h => hrC (h ▸ hy), Finset.mem_univ y⟩
    unfold parentCost
    rw [← Finset.sum_sdiff hsub, ← Finset.sum_sdiff hsub]
    congr 1
    · refine Finset.sum_congr rfl fun v hv => ?_
      have hvC : v ∉ C := (Finset.mem_sdiff.mp hv).2
      by_cases hqv : q v = x0
      · obtain ⟨y, -, -, hbi, hpy⟩ := hpO v hvC hqv
        rw [hpy, hqv]
        simp [contractCost, hvC, hbi]
      · rw [hpO' v hvC hqv]
        simp [contractCost, hvC, hqv]
    · rw [← Finset.add_sum_erase C _ hxsC, ← Finset.add_sum_erase C _ hx0,
        hpC xs hxsC, ite_eq_left rfl]
      have h0 : ∑ v ∈ C.erase x0, contractCost a c f C x0 v (q v) = 0 :=
        Finset.sum_eq_zero fun v hv => by
          simp [contractCost, Finset.mem_of_mem_erase hv, Finset.ne_of_mem_erase hv]
      have h1 : ∑ v ∈ C.erase xs, c v (p v) = ∑ v ∈ C.erase xs, c v (f v) :=
        Finset.sum_congr rfl fun v hv => by
          rw [hpC v (Finset.mem_of_mem_erase hv), ite_eq_right (Finset.ne_of_mem_erase hv)]
      rw [h0, h1, add_zero]
      simp [contractCost, hx0, hbo, exitCost]

/-- **Exchange.** If every vertex `v ≠ r` selects a cheapest arc `v → f v`, then every
arborescence `t` of the original instance contracts to an arborescence of the contracted instance
of at most the same cost: the vertex of `C` closest to `r` in `t` keeps its arc out of `C`, the
other vertices of `C` point to `r`, and arcs into `C` are redirected to `x0`. -/
theorem exists_contract_le [IsOrderedAddMonoid β]
    (hfmin : ∀ v, v ≠ r → ∀ w, a v w = true → w ≠ v → c v (f v) ≤ c v w)
    (hx0 : x0 ∈ C) (hrC : r ∉ C) {t : V → V}
    (ht : IsInArborescenceParent (fun u w => a u w = true) r t) :
    ∃ q, IsInArborescenceParent (fun u w => contractAdj a C x0 r u w = true) r q ∧
      parentCost (contractCost a c f C x0) r q ≤ parentCost c r t := by
  classical
  have hCr : ∀ y ∈ C, y ≠ r := fun y hy h => hrC (h ▸ hy)
  have hexk : ∃ k, ∃ y ∈ C, t^[k] y = r := by
    obtain ⟨n, hn⟩ := ht.reach x0
    exact ⟨n, x0, hx0, hn⟩
  obtain ⟨x, hxC, hxk⟩ := Nat.find_spec hexk
  have hmin : ∀ j < Nat.find hexk, ∀ y ∈ C, t^[j] y ≠ r := fun j hj y hy h =>
    Nat.find_min hexk hj ⟨y, hy, h⟩
  -- below the least distance from `C` to `r`, `t`-paths to `r` avoid `C`
  have havoid : ∀ w j, j < Nat.find hexk → t^[j] w = r → ∀ i ≤ j, t^[i] w ∉ C := by
    intro w j hj hw i hi hiC
    apply hmin (j - i) (by omega) _ hiC
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hi, hw]
  obtain ⟨k', hk'⟩ : ∃ k', Nat.find hexk = k' + 1 := by
    rcases h : Nat.find hexk with _ | k'
    · rw [h] at hxk; exact absurd hxk (hCr x hxC)
    · exact ⟨k', rfl⟩
  have htx : t^[k'] (t x) = r := by
    rw [← Function.iterate_succ_apply]
    rw [hk'] at hxk
    exact hxk
  have htxC : t x ∉ C := havoid (t x) k' (by omega) htx 0 (Nat.zero_le _)
  let q : V → V := fun v =>
    if v ∈ C then (if v = x0 then t x else r) else if t v ∈ C then x0 else t v
  have hqC : ∀ v ∈ C, q v = if v = x0 then t x else r := fun v hv => by simp [q, hv]
  have hqO : ∀ v ∉ C, q v = if t v ∈ C then x0 else t v := fun v hv => by simp [q, hv]
  have htr : t r = r := ht.root
  have hq_r : q r = r := by rw [hqO r hrC, htr, ite_eq_right hrC]
  -- reachability from the exit vertex
  have hQ : ∀ j < Nat.find hexk, ∀ w, t^[j] w = r → ∃ n, q^[n] w = r := by
    intro j
    induction j with
    | zero => intro _ w hw; exact ⟨0, hw⟩
    | succ j ih =>
      intro hj w hw
      have hw0 := havoid w (j + 1) hj hw 0 (Nat.zero_le _)
      have hw1 := havoid w (j + 1) hj hw 1 (by omega)
      simp only [Function.iterate_zero, id_eq, Function.iterate_one] at hw0 hw1
      rw [Function.iterate_succ_apply] at hw
      obtain ⟨n, hn⟩ := ih (by omega) (t w) hw
      refine ⟨n + 1, ?_⟩
      rw [Function.iterate_succ_apply, hqO w hw0, ite_eq_right hw1, hn]
  have hqx0 : ∃ n, q^[n] x0 = r := by
    obtain ⟨n, hn⟩ := hQ k' (by omega) (t x) htx
    exact ⟨n + 1, by rw [Function.iterate_succ_apply, hqC x0 hx0, ite_eq_left rfl, hn]⟩
  have hqreach : ∀ v, ∃ n, q^[n] v = r := by
    intro v
    by_cases hvC : v ∈ C
    · by_cases hvx : v = x0
      · exact hvx ▸ hqx0
      · exact ⟨1, by rw [Function.iterate_one, hqC v hvC, ite_eq_right hvx]⟩
    · obtain ⟨d, hd⟩ := ht.reach v
      induction d generalizing v with
      | zero => exact ⟨0, hd⟩
      | succ d ih =>
        rw [Function.iterate_succ_apply] at hd
        by_cases htv : t v ∈ C
        · obtain ⟨n, hn⟩ := hqx0
          exact ⟨n + 1, by rw [Function.iterate_succ_apply, hqO v hvC, ite_eq_left htv, hn]⟩
        · obtain ⟨n, hn⟩ := ih (t v) htv hd
          exact ⟨n + 1, by rw [Function.iterate_succ_apply, hqO v hvC, ite_eq_right htv, hn]⟩
  have hqadj : ∀ v, v ≠ r → contractAdj a C x0 r v (q v) = true := by
    intro v hvr
    by_cases hvC : v ∈ C
    · rw [hqC v hvC]
      split_ifs with hvx
      · subst hvx
        exact (contractAdj_rep_iff hvC).mpr ⟨htxC, x, hxC, ht.adj x (hCr x hxC)⟩
      · exact (contractAdj_mem_iff hvC hvx).mpr rfl
    · rw [hqO v hvC]
      split_ifs with htv
      · exact (contractAdj_out_mem_iff hvC hx0).mpr ⟨rfl, t v, htv, ht.adj v hvr⟩
      · exact (contractAdj_out_out_iff hvC htv).mpr (ht.adj v hvr)
  refine ⟨q, ⟨hq_r, hqadj, hqreach⟩, ?_⟩
  have hsub : C ⊆ Finset.univ.erase r := fun y hy =>
    Finset.mem_erase.mpr ⟨hCr y hy, Finset.mem_univ y⟩
  unfold parentCost
  rw [← Finset.sum_sdiff hsub, ← Finset.sum_sdiff hsub]
  apply add_le_add
  · refine Finset.sum_le_sum fun v hv => ?_
    have hvC : v ∉ C := (Finset.mem_sdiff.mp hv).2
    have hvr : v ≠ r := Finset.ne_of_mem_erase (Finset.mem_sdiff.mp hv).1
    rw [hqO v hvC]
    split_ifs with htv
    · obtain ⟨y, hbi, -, -, hymin⟩ := bestEntry_spec (c := c) ⟨t v, htv, ht.adj v hvr⟩
      have : contractCost a c f C x0 v x0 = c v y := by simp [contractCost, hvC, hbi]
      rw [this]
      exact hymin _ htv (ht.adj v hvr)
    · have htx0 : t v ≠ x0 := fun h => htv (h ▸ hx0)
      simp [contractCost, hvC, htx0]
  · rw [← Finset.add_sum_erase C _ hx0, hqC x0 hx0, ite_eq_left rfl]
    have h0 : ∑ v ∈ C.erase x0, contractCost a c f C x0 v (q v) = 0 :=
      Finset.sum_eq_zero fun v hv => by
        simp [contractCost, Finset.mem_of_mem_erase hv, Finset.ne_of_mem_erase hv]
    rw [h0, add_zero]
    obtain ⟨xs, hbo, -, -, hxsmin⟩ :=
      bestExit_spec (c := c) (f := f) ⟨x, hxC, ht.adj x (hCr x hxC)⟩
    have : contractCost a c f C x0 x0 (t x) = exitCost c f C xs (t x) := by
      simp [contractCost, hx0, hbo]
    rw [this]
    refine (hxsmin x hxC (ht.adj x (hCr x hxC))).trans ?_
    rw [exitCost, ← Finset.add_sum_erase C _ hxC]
    refine add_le_add le_rfl (Finset.sum_le_sum fun y hy => ?_)
    have hyC := Finset.mem_of_mem_erase hy
    exact hfmin y (hCr y hyC) _ (ht.adj y (hCr y hyC)) (ht.ne (hCr y hyC))

end Contract

/-! ### The algorithm -/

section Main

variable [FinEnum V]

/-- The vertices other than `r` with an arc to a vertex other than themselves and `r`. Contraction
strictly shrinks this set (`liveVertices_ssubset`). -/
private def liveVertices (a : V → V → Bool) (r : V) : Finset V :=
  Finset.univ.filter fun v => v ≠ r ∧ ∃ w, w ≠ v ∧ w ≠ r ∧ a v w = true

private theorem liveVertices_ssubset {a : V → V → Bool} {f : V → V} {C : Finset V} {x0 r : V}
    (hfC : ∀ y ∈ C, f y ∈ C) (hfa : ∀ y ∈ C, a y (f y) = true ∧ f y ≠ y)
    (hx0 : x0 ∈ C) (hrC : r ∉ C) :
    liveVertices (contractAdj a C x0 r) r ⊂ liveVertices a r := by
  have hCr : ∀ y ∈ C, y ≠ r := fun y hy h => hrC (h ▸ hy)
  have hsub : liveVertices (contractAdj a C x0 r) r ⊆ liveVertices a r := by
    intro v hv
    obtain ⟨hvr, w, hwv, hwr, hvw⟩ := (Finset.mem_filter.mp hv).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvr, ?_⟩
    by_cases hvC : v ∈ C
    · exact ⟨f v, (hfa v hvC).2, hCr _ (hfC v hvC), (hfa v hvC).1⟩
    · by_cases hwC : w ∈ C
      · obtain ⟨-, y, hyC, hy⟩ := (contractAdj_out_mem_iff hvC hwC).mp hvw
        exact ⟨y, fun h => hvC (h ▸ hyC), hCr y hyC, hy⟩
      · exact ⟨w, hwv, hwr, (contractAdj_out_out_iff hvC hwC).mp hvw⟩
  have hz := hfC x0 hx0
  refine (Finset.ssubset_iff_of_subset hsub).mpr ⟨f x0, ?_, ?_⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hCr _ hz, f (f x0), (hfa _ hz).2,
      hCr _ (hfC _ hz), (hfa _ hz).1⟩
  · intro h
    obtain ⟨-, w, -, hwr, hadj⟩ := (Finset.mem_filter.mp h).2
    exact hwr ((contractAdj_mem_iff hz (hfa x0 hx0).2).mp hadj)

private theorem liveVertices_card_lt (a : V → V → Bool) (r : V) :
    (liveVertices a r).card < FinEnum.card V := by
  rw [FinEnum.card_eq_fintypeCard, ← Finset.card_univ]
  refine Finset.card_lt_card ⟨Finset.subset_univ _, fun h => ?_⟩
  exact (Finset.mem_filter.mp (h (Finset.mem_univ r))).2.1 rfl

variable [LinearOrder β] [AddCommMonoid β]

/-- The Chu–Liu/Edmonds recursion with fuel `n`, on arcs `a` and costs `c`: select cheapest
arcs; return them if they form no cycle, otherwise contract a cycle, recurse and expand. -/
@[expose] def edmondsAux (r : V) : ℕ → (V → V → Bool) → (V → V → β) → Option (V → V)
  | 0, _, _ => none
  | n + 1, a, c =>
    if ∀ v, v ≠ r → candidates a v ≠ [] then
      match findCycle r (cheapestParent a c r) with
      | none => some (cheapestParent a c r)
      | some x0 =>
        (edmondsAux r n (contractAdj a (cycleOf (cheapestParent a c r) x0) x0 r)
          (contractCost a c (cheapestParent a c r) (cycleOf (cheapestParent a c r) x0) x0)).map
          (expandParent a c (cheapestParent a c r) (cycleOf (cheapestParent a c r) x0) x0)
    else none

/-- Correctness of `edmondsAux` with enough fuel. -/
private theorem edmondsAux_spec [IsOrderedAddMonoid β] (r : V) :
    ∀ (n : ℕ) (a : V → V → Bool) (c : V → V → β), (liveVertices a r).card < n →
      (∀ p, edmondsAux r n a c = some p →
        IsInArborescenceParent (fun u w => a u w = true) r p ∧
        ∀ t, IsInArborescenceParent (fun u w => a u w = true) r t →
          parentCost c r p ≤ parentCost c r t) ∧
      (edmondsAux r n a c = none →
        ∀ t, ¬ IsInArborescenceParent (fun u w => a u w = true) r t)
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, a, c, hn => by
    by_cases hfeas : ∀ v, v ≠ r → candidates a v ≠ []
    · have hsel := fun v (hv : v ≠ r) => cheapestParent_spec a c r hv (hfeas v hv)
      cases hcyc : findCycle r (cheapestParent a c r) with
      | none =>
        have heq : edmondsAux r (n + 1) a c = some (cheapestParent a c r) := by
          rw [edmondsAux, ite_eq_left hfeas, hcyc]
        have harb :
            IsInArborescenceParent (fun u w => a u w = true) r (cheapestParent a c r) :=
          ⟨cheapestParent_root a c r, fun v hv => (hsel v hv).1, reach_of_findCycle_none r hcyc⟩
        refine ⟨fun p hp => ?_, fun hp => ?_⟩
        · rw [heq] at hp
          obtain rfl := Option.some_injective _ hp
          refine ⟨harb, fun t ht => Finset.sum_le_sum fun v hv => ?_⟩
          have hvr := Finset.ne_of_mem_erase hv
          exact (hsel v hvr).2.2 _ (ht.adj v hvr) (ht.ne hvr)
        · rw [heq] at hp
          exact absurd hp (Option.some_ne_none _)
      | some x0 =>
        have heq : edmondsAux r (n + 1) a c =
            (edmondsAux r n (contractAdj a (cycleOf (cheapestParent a c r) x0) x0 r)
              (contractCost a c (cheapestParent a c r) (cycleOf (cheapestParent a c r) x0)
                x0)).map
              (expandParent a c (cheapestParent a c r) (cycleOf (cheapestParent a c r) x0)
                x0) := by
          rw [edmondsAux, ite_eq_left hfeas, hcyc]
        obtain ⟨hx0r, k, hk, hper⟩ := findCycle_some r hcyc
        set f := cheapestParent a c r with hf
        set C := cycleOf f x0 with hC
        have hm : Function.IsPeriodicPt f (k + 1) x0 := hper
        have hm0 : 0 < k + 1 := Nat.succ_pos k
        have hmc : k + 1 ≤ FinEnum.card V := hk
        have hx0C : x0 ∈ C := iterate_mem_cycleOf hm hm0 hmc 0
        have hfC : ∀ y ∈ C, f y ∈ C := fun y hy => map_mem_cycleOf hm hm0 hmc hy
        have hrC : r ∉ C := root_notMem_cycleOf r (cheapestParent_root a c r) hx0r hm hm0 hmc
        have hCr : ∀ y ∈ C, y ≠ r := fun y hy h => hrC (h ▸ hy)
        have hfa : ∀ y ∈ C, a y (f y) = true ∧ f y ≠ y := fun y hy =>
          ⟨(hsel y (hCr y hy)).1, (hsel y (hCr y hy)).2.1⟩
        have hreach : ∀ y ∈ C, ∀ z ∈ C, ∃ n, f^[n] y = z := fun y hy z hz =>
          cycleOf_reach hm hm0 hy hz
        have hfmin : ∀ v, v ≠ r → ∀ w, a v w = true → w ≠ v → c v (f v) ≤ c v w :=
          fun v hv => (hsel v hv).2.2
        have hlt : (liveVertices (contractAdj a C x0 r) r).card < n := by
          have := Finset.card_lt_card (liveVertices_ssubset hfC hfa hx0C hrC)
          omega
        obtain ⟨ih1, ih2⟩ :=
          edmondsAux_spec r n (contractAdj a C x0 r) (contractCost a c f C x0) hlt
        refine ⟨fun p hp => ?_, fun hp t ht => ?_⟩
        · rw [heq] at hp
          obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp hp
          obtain ⟨hqarb, hqmin⟩ := ih1 q hq
          obtain ⟨hparb, hcost⟩ :=
            expandParent_spec (c := c) (fun y hy => (hfa y hy).1) hfC hx0C hrC hreach hqarb
          refine ⟨hparb, fun t ht => ?_⟩
          obtain ⟨q', hq', hq'c⟩ := exists_contract_le hfmin hx0C hrC ht
          rw [hcost]
          exact (hqmin q' hq').trans hq'c
        · rw [heq] at hp
          obtain ⟨q', hq', -⟩ := exists_contract_le hfmin hx0C hrC ht
          exact ih2 (Option.map_eq_none_iff.mp hp) q' hq'
    · have heq : edmondsAux r (n + 1) a c = none := by
        rw [edmondsAux, ite_eq_right hfeas]
      refine ⟨fun p hp => by rw [heq] at hp; exact absurd hp (by simp), fun _ t ht => ?_⟩
      push Not at hfeas
      obtain ⟨v, hvr, hv⟩ := hfeas
      have hmem : t v ∈ candidates a v := (mem_candidates a).mpr ⟨ht.adj v hvr, ht.ne hvr⟩
      rw [hv] at hmem
      exact List.not_mem_nil hmem

/-- **The Chu–Liu/Edmonds algorithm**: a minimum-cost spanning in-arborescence of `G` rooted at
`r`, as a parent function, or `none` if `G` has no spanning in-arborescence rooted at `r`. -/
@[expose] def edmonds (G : Digraph V) [DecidableRel G.Adj] (c : V → V → β) (r : V) :
    Option (V → V) :=
  edmondsAux r (FinEnum.card V) (fun u w => decide (G.Adj u w)) c

/-- The Chu–Liu/Edmonds algorithm for out-arborescences, with arcs directed away from the root:
`p v → v` is an arc of `G` for `v ≠ r`, and the cost is `∑ v ≠ r, c (p v) v`. -/
@[expose] def edmondsOut (G : Digraph V) [DecidableRel G.Adj] (c : V → V → β) (r : V) :
    Option (V → V) :=
  edmondsAux r (FinEnum.card V) (fun u w => decide (G.Adj w u)) (fun u w => c w u)

variable [IsOrderedAddMonoid β] {G : Digraph V} [DecidableRel G.Adj] {c : V → V → β} {r : V}

omit [FinEnum V] in
private theorem isInArborescenceParent_decide {R : V → V → Prop} [DecidableRel R] {p : V → V} :
    IsInArborescenceParent (fun u w => decide (R u w) = true) r p ↔
      IsInArborescenceParent R r p := by
  simp only [decide_eq_true_eq]

/-- **Correctness of Chu–Liu/Edmonds.** If `edmonds G c r = some p`, then `p` is the parent
function of a spanning in-arborescence of `G` rooted at `r` whose cost is at most that of every
other one; if `edmonds G c r = none`, then `G` has no spanning in-arborescence rooted at `r`. -/
theorem edmonds_spec :
    (∀ p, edmonds G c r = some p →
      IsInArborescenceParent G.Adj r p ∧
        ∀ t, IsInArborescenceParent G.Adj r t → parentCost c r p ≤ parentCost c r t) ∧
    (edmonds G c r = none → ∀ t, ¬ IsInArborescenceParent G.Adj r t) := by
  obtain ⟨h1, h2⟩ :=
    edmondsAux_spec r _ (fun u w => decide (G.Adj u w)) c (liveVertices_card_lt _ r)
  simp only [isInArborescenceParent_decide] at h1 h2
  exact ⟨h1, h2⟩

/-- `edmonds` fails exactly when there is no spanning in-arborescence rooted at `r`. -/
theorem edmonds_eq_none_iff :
    edmonds G c r = none ↔ ∀ t, ¬ IsInArborescenceParent G.Adj r t := by
  refine ⟨edmonds_spec.2, fun h => ?_⟩
  cases hp : edmonds G c r with
  | none => rfl
  | some p => exact absurd (edmonds_spec.1 p hp).1 (h p)

/-- **Optimality over spanning in-arborescences.** If `edmonds G c r = some p`, then the digraph
of `p` is a spanning in-arborescence of `G` rooted at `r` (`Digraph.IsInArborescence`), and its
arc cost is at most that of every spanning in-arborescence `T ≤ G` rooted at `r`. -/
theorem edmonds_optimal {p : V → V} (hp : edmonds G c r = some p) :
    (Digraph.parentDigraph r p).IsInArborescence r ∧ Digraph.parentDigraph r p ≤ G ∧
      ∀ (T : Digraph V) [DecidableRel T.Adj], T.IsInArborescence r → T ≤ G →
        arcCost (Digraph.parentDigraph r p) c ≤ arcCost T c := by
  obtain ⟨hpa, hmin⟩ := edmonds_spec.1 p hp
  obtain ⟨h1, h2⟩ := (isInArborescenceParent_iff hpa.root).mp hpa
  refine ⟨h1, h2, fun T _ hT hTG => ?_⟩
  obtain ⟨t, htr, rfl⟩ := hT.exists_parentDigraph_eq
  have := hmin t ((isInArborescenceParent_iff htr).mpr ⟨hT, hTG⟩)
  rw [arcCost_parentDigraph]
  convert this using 1
  convert arcCost_parentDigraph r t c

/-- **Correctness for out-arborescences.** If `edmondsOut G c r = some p`, then every vertex
`v ≠ r` has an arc `p v → v` of `G`, iterating `p` reaches `r`, and the cost
`∑ v ≠ r, c (p v) v` is least among all such `p`; if it is `none`, there is no such `p`. -/
theorem edmondsOut_spec :
    (∀ p, edmondsOut G c r = some p →
      IsInArborescenceParent (fun u w => G.Adj w u) r p ∧
        ∀ t, IsInArborescenceParent (fun u w => G.Adj w u) r t →
          parentCost (fun u w => c w u) r p ≤ parentCost (fun u w => c w u) r t) ∧
    (edmondsOut G c r = none → ∀ t, ¬ IsInArborescenceParent (fun u w => G.Adj w u) r t) := by
  obtain ⟨h1, h2⟩ := edmondsAux_spec r _ (fun u w => decide (G.Adj w u)) (fun u w => c w u)
    (liveVertices_card_lt _ r)
  simp only [decide_eq_true_eq] at h1 h2
  exact ⟨h1, h2⟩

end Main

end Cslib.Algorithms.Lean.Arborescence
