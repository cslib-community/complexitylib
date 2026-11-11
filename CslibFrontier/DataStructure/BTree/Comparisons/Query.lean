/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.BTree.Height
public import CslibFrontier.DataStructure.BTree.MinMax
public import CslibFrontier.DataStructure.BTree.PredSucc
public import CslibFrontier.DataStructure.BTree.Rank
public import Cslib.Algorithms.Lean.Query.Bounds
public import Cslib.Algorithms.Lean.Query.Sort.LEQuery

/-!
# Comparison costs of B-tree point queries

The point queries of `Cslib.DataStructure.BTree` are defined once over a monad,
with a comparator and a node-visit action. This file instantiates them in
CSLib's query-complexity framework, at `FreeM (LEQuery α)` with the
comparison query `LEQuery.ask` and the trivial `visit := pure ()`,
so that every key comparison is a query and node visits are free: `lookupQ`, `containsQ`,
`minQ`, `maxQ`, `predQ`, `succQ` and `rankQ`. Counting is structural: a program parametric in
the oracle cannot compare keys without asking.

Applied to `FreeM.isMonadHom_pure_eval`, the transfer lemmas `Cslib.IsMonadHom.map_lookupM` and
its siblings give `eval_lookupQ` and its siblings: under `orderOracle`, the oracle of the order
on the keys, each query evaluates to the pure query.

A query scans the keys of a node, one comparison per key passed, and descends into one child;
lookup spends one more comparison to test equality. `le_mul_height_of_scan` turns such a
per-node bound of `rest.length + 1` into `2 * t * height` on a tree whose root holds at most
`2 * t - 1` keys and whose children are occupied, which is every well-formed tree. The
resulting bounds, `countQueries_lookupQ_le` and its siblings, hold for every oracle, since the
shape of the tree does not depend on the answers; `lookupQ_upperBound` and its siblings restate
them as `Cslib.Query.UpperBound` over well-formed inputs. The
minimum and maximum make no comparisons at all. `countQueries_slotM_le` bounds the within-node
linear search by one comparison per key. The bound is the comparison analysis of B-TREE-SEARCH
in [CLRS2009], Section 18.2.

## Main definitions

* `lookupQ`, `containsQ`, `minQ`, `maxQ`, `predQ`, `succQ`, `rankQ`: B-tree point queries counting
  comparisons.

## Main results

* `countQueries_lookupQ_le`: the number of comparisons made by `lookupQ` is at most
  `2 * t * height`.
* `eval_lookupQ`: the value of `lookupQ` evaluated at the order oracle matches
  `lookup`.
* (and similarly for the other queries)

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Chapter 18][CLRS2009]

Ported from cslib-community/EpsilonEridani PR #39 at commit 9425389c8.
-/

public section

open Cslib (FreeM)
open Cslib.Query (LEQuery UpperBound)

namespace Cslib.DataStructure.BTree

section Comparisons

variable {α β : Type} {t : ℕ} {tr : BTree α β}

/-- Lookup, issuing one query per key comparison. -/
def lookupQ (k : α) (tr : BTree α β) : FreeM (LEQuery α) (Option β) :=
  lookupM LEQuery.ask (pure ()) k tr

/-- `lookupQ` is `lookupM` with the comparison query and free visits. -/
theorem lookupQ_def (k : α) : lookupQ k tr = lookupM LEQuery.ask (pure ()) k tr := (rfl)

/-- Membership test, issuing one query per key comparison. -/
def containsQ (k : α) (tr : BTree α β) : FreeM (LEQuery α) Bool :=
  containsM LEQuery.ask (pure ()) k tr

/-- `containsQ` is `containsM` with the comparison query and free visits. -/
theorem containsQ_def (k : α) : containsQ k tr = containsM LEQuery.ask (pure ()) k tr := (rfl)

/-- Least entry in the comparison model, where it asks nothing. -/
def minQ (tr : BTree α β) : FreeM (LEQuery α) (Option (α × β)) := minM (pure ()) tr

/-- `minQ` is `minM` with free visits. -/
theorem minQ_def : minQ tr = minM (pure ()) tr := (rfl)

/-- Greatest entry in the comparison model, where it asks nothing. -/
def maxQ (tr : BTree α β) : FreeM (LEQuery α) (Option (α × β)) := maxM (pure ()) tr

/-- `maxQ` is `maxM` with free visits. -/
theorem maxQ_def : maxQ tr = maxM (pure ()) tr := (rfl)

/-- Strict predecessor, issuing one query per key comparison. -/
def predQ (k : α) (tr : BTree α β) : FreeM (LEQuery α) (Option (α × β)) :=
  predM LEQuery.ask (pure ()) k tr

/-- `predQ` is `predM` with the comparison query and free visits. -/
theorem predQ_def (k : α) : predQ k tr = predM LEQuery.ask (pure ()) k tr := (rfl)

/-- Strict successor, issuing one query per key comparison. -/
def succQ (k : α) (tr : BTree α β) : FreeM (LEQuery α) (Option (α × β)) :=
  succM LEQuery.ask (pure ()) k tr

/-- `succQ` is `succM` with the comparison query and free visits. -/
theorem succQ_def (k : α) : succQ k tr = succM LEQuery.ask (pure ()) k tr := (rfl)

/-- Rank, issuing one query per key comparison. -/
def rankQ (k : α) (tr : BTree α β) : FreeM (LEQuery α) ℕ := rankM LEQuery.ask (pure ()) k tr

/-- `rankQ` is `rankM` with the comparison query and free visits. -/
theorem rankQ_def (k : α) : rankQ k tr = rankM LEQuery.ask (pure ()) k tr := (rfl)

/-! ### Transfer: `eval` at the order's oracle is the pure operation -/

/-- Under any oracle, `minQ` evaluates to `min?`. -/
@[simp] theorem eval_minQ (oracle : {ι : Type} → LEQuery α ι → ι) :
    (minQ tr).eval oracle = min? tr := by
  simpa [min?_def, minQ] using
    Id.ext_iff.1 ((FreeM.isMonadHom_pure_eval oracle).map_minM (pure ()) tr)

/-- Under any oracle, `maxQ` evaluates to `max?`. -/
@[simp] theorem eval_maxQ (oracle : {ι : Type} → LEQuery α ι → ι) :
    (maxQ tr).eval oracle = max? tr := by
  simpa [max?_def, maxQ] using
    Id.ext_iff.1 ((FreeM.isMonadHom_pure_eval oracle).map_maxM (pure ()) tr)

section Transfer

variable [LinearOrder α]

/-- The oracle of the order on the keys. -/
abbrev orderOracle : {ι : Type} → LEQuery α ι → ι :=
  LEQuery.oracleOf fun a b => decide (a ≤ b)

/-- Under the order's oracle, `lookupQ` evaluates to `lookup`. -/
@[simp] theorem eval_lookupQ (k : α) : (lookupQ k tr).eval orderOracle = lookup k tr := by
  simpa [lookup_def, lookupQ] using
    Id.ext_iff.1 ((FreeM.isMonadHom_pure_eval orderOracle).map_lookupM LEQuery.ask (pure ()) k tr)

/-- Under the order's oracle, `containsQ` evaluates to `contains`. -/
@[simp] theorem eval_containsQ (k : α) :
    (containsQ k tr).eval orderOracle = contains k tr := by
  simp [containsQ, containsM, ← lookupQ_def]

/-- Under the order's oracle, `predQ` evaluates to `pred?`. -/
@[simp] theorem eval_predQ (k : α) : (predQ k tr).eval orderOracle = pred? k tr := by
  simpa [pred?_def, predQ] using
    Id.ext_iff.1 ((FreeM.isMonadHom_pure_eval orderOracle).map_predM LEQuery.ask (pure ()) k tr)

/-- Under the order's oracle, `succQ` evaluates to `succ?`. -/
@[simp] theorem eval_succQ (k : α) : (succQ k tr).eval orderOracle = succ? k tr := by
  simpa [succ?_def, succQ] using
    Id.ext_iff.1 ((FreeM.isMonadHom_pure_eval orderOracle).map_succM LEQuery.ask (pure ()) k tr)

/-- Under the order's oracle, `rankQ` evaluates to `rank`. -/
@[simp] theorem eval_rankQ (k : α) : (rankQ k tr).eval orderOracle = rank k tr := by
  simpa [rank_def, rankQ] using
    Id.ext_iff.1 ((FreeM.isMonadHom_pure_eval orderOracle).map_rankM LEQuery.ask (pure ()) k tr)

end Transfer

/-! ### Comparison counts -/

variable (oracle : {ι : Type} → LEQuery α ι → ι)

/-- The within-node linear search makes at most one comparison per key. -/
theorem countQueries_slotM_le (k : α) (rest : List (α × β × BTree α β)) :
    (slotM LEQuery.ask k rest).countQueries oracle ≤ rest.length := by
  induction rest with
  | nil => simp only [slotM, FreeM.countQueries_pure, List.length_nil, Std.le_refl]
  | cons e rest ih =>
    obtain ⟨k', v, c⟩ := e
    simp only [slotM, bind_pure_comp, FreeM.countQueries_bind, FreeM.countQueries_lift,
      ↓FreeM.countQueries_ite, FreeM.eval_lift, FreeM.countQueries_pure, FreeM.countQueries_map,
      List.length_cons]
    split <;> omega

/-- The minimum search makes no comparison. -/
@[simp] theorem countQueries_minQ (tr : BTree α β) : (minQ tr).countQueries oracle = 0 := by
  rw [minQ]
  fun_induction minM (pure () : FreeM (LEQuery α) Unit) tr with
  | case1 => simp
  | case2 first rest ih =>
    simp only [pure_bind, FreeM.countQueries_bind, ih, zero_add]
    split <;> simp

/-- The maximum search makes no comparison. -/
@[simp] theorem countQueries_maxQ (tr : BTree α β) : (maxQ tr).countQueries oracle = 0 := by
  match tr with
  | .leaf => simp [maxQ, maxM_leaf]
  | .node first [] =>
    simpa [maxQ, maxM_node_nil] using countQueries_maxQ first
  | .node first [(k, v, c)] =>
    have := countQueries_maxQ c
    rw [maxQ] at this
    simp only [maxQ, maxM_node_singleton, FreeM.countQueries_bind, FreeM.countQueries_pure, this]
    split <;> simp
  | .node first ((k, v, c) :: e :: rest) =>
    simpa [maxQ, maxM_node_cons_cons] using countQueries_maxQ (.node c (e :: rest))
termination_by sizeOf tr

/-- Lookup in the empty tree makes no comparison. -/
@[simp] theorem countQueries_lookupQ_leaf (k : α) :
    (lookupQ k (.leaf : BTree α β)).countQueries oracle = 0 := by
  simp [lookupQ, lookupM]

/-- Predecessor search in the empty tree makes no comparison. -/
@[simp] theorem countQueries_predQ_leaf (k : α) :
    (predQ k (.leaf : BTree α β)).countQueries oracle = 0 := by
  simp [predQ, predM_leaf]

/-- Successor search in the empty tree makes no comparison. -/
@[simp] theorem countQueries_succQ_leaf (k : α) :
    (succQ k (.leaf : BTree α β)).countQueries oracle = 0 := by
  simp [succQ, succM_leaf]

/-- Rank in the empty tree makes no comparison. -/
@[simp] theorem countQueries_rankQ_leaf (k : α) :
    (rankQ k (.leaf : BTree α β)).countQueries oracle = 0 := by
  simp [rankQ, rankM_leaf]

/-- Lookup at a node makes at most one comparison per key and one more beyond what it makes in
the child it descends into. -/
theorem countQueries_lookupQ_node_le (k : α) (first : BTree α β)
    (rest : List (α × β × BTree α β)) {B : ℕ}
    (hB : ∀ c ∈ (node first rest).children, (lookupQ k c).countQueries oracle ≤ B) :
    (lookupQ k (node first rest)).countQueries oracle ≤ rest.length + 1 + B := by
  simp only [lookupQ] at hB ⊢
  induction rest generalizing first with
  | nil =>
    have := hB first List.mem_cons_self
    rw [lookupM]
    simp
    omega
  | cons e rest ih =>
    obtain ⟨k', v, c⟩ := e
    have h₁ := hB first List.mem_cons_self
    have h₂ := ih c fun c' hc' => hB c' (children_node_subset_children_node_cons hc')
    rw [lookupM]
    simp only [FreeM.countQueries_bind, FreeM.countQueries_lift, FreeM.eval_lift]
    by_cases h₃ : oracle (LEQuery.le k k') = true <;>
      by_cases h₄ : oracle (LEQuery.le k' k) = true <;> simp [h₃, h₄] <;> omega

/-- Predecessor search at a node makes at most one more comparison than the node has keys, beyond
what it makes in the child it descends into. -/
theorem countQueries_predQ_node_le (k : α) (first : BTree α β)
    (rest : List (α × β × BTree α β)) {B : ℕ}
    (hB : ∀ c ∈ (node first rest).children, (predQ k c).countQueries oracle ≤ B) :
    (predQ k (node first rest)).countQueries oracle ≤ rest.length + 1 + B := by
  simp only [predQ] at hB ⊢
  induction rest generalizing first with
  | nil =>
    have := hB first List.mem_cons_self
    simp [predM_node_nil]
    omega
  | cons e rest ih =>
    obtain ⟨k', v, c⟩ := e
    have h₁ := hB first List.mem_cons_self
    have h₂ := ih c fun c' hc' => hB c' (children_node_subset_children_node_cons hc')
    simp only [predM_node_cons, pure_bind, Option.or_some, bind_pure_comp,
      FreeM.countQueries_bind, FreeM.countQueries_lift, ↓FreeM.countQueries_ite, FreeM.eval_lift,
      FreeM.countQueries_map, List.length_cons, ge_iff_le]
    split_ifs <;> omega

/-- Successor search at a node makes at most one more comparison than the node has keys, beyond
what it makes in the child it descends into. -/
theorem countQueries_succQ_node_le (k : α) (first : BTree α β)
    (rest : List (α × β × BTree α β)) {B : ℕ}
    (hB : ∀ c ∈ (node first rest).children, (succQ k c).countQueries oracle ≤ B) :
    (succQ k (node first rest)).countQueries oracle ≤ rest.length + 1 + B := by
  simp only [succQ] at hB ⊢
  induction rest generalizing first with
  | nil =>
    have := hB first List.mem_cons_self
    simp [succM_node_nil]
    omega
  | cons e rest ih =>
    obtain ⟨k', v, c⟩ := e
    have h₁ := hB first List.mem_cons_self
    have h₂ := ih c fun c' hc' => hB c' (children_node_subset_children_node_cons hc')
    simp only [succM_node_cons, Option.or_some, bind_pure_comp, pure_bind,
      FreeM.countQueries_bind, FreeM.countQueries_lift, ↓FreeM.countQueries_ite, FreeM.eval_lift,
      FreeM.countQueries_map, List.length_cons, ge_iff_le]
    split_ifs <;> omega

/-- Rank at a node makes at most one more comparison than the node has keys, beyond what it
makes in the child it descends into. -/
theorem countQueries_rankQ_node_le (k : α) (first : BTree α β)
    (rest : List (α × β × BTree α β)) {B : ℕ}
    (hB : ∀ c ∈ (node first rest).children, (rankQ k c).countQueries oracle ≤ B) :
    (rankQ k (node first rest)).countQueries oracle ≤ rest.length + 1 + B := by
  simp only [rankQ] at hB ⊢
  induction rest generalizing first with
  | nil =>
    have := hB first List.mem_cons_self
    simp [rankM_node_nil]
    omega
  | cons e rest ih =>
    obtain ⟨k', v, c⟩ := e
    have h₁ := hB first List.mem_cons_self
    have h₂ := ih c fun c' hc' => hB c' (children_node_subset_children_node_cons hc')
    simp only [rankM_node_cons, pure_bind, bind_pure_comp, FreeM.countQueries_bind,
      FreeM.countQueries_lift, ↓FreeM.countQueries_ite, FreeM.eval_lift, FreeM.countQueries_map,
      List.length_cons, ge_iff_le]
    split_ifs <;> omega

/-- The membership test makes as many comparisons as lookup. -/
@[simp] theorem countQueries_containsQ (k : α) :
    (containsQ k tr).countQueries oracle = (lookupQ k tr).countQueries oracle := by
  simp [containsQ, containsM, lookupQ]

/-! ### Comparison bounds -/

section Bounds

variable [LinearOrder α]

/-- Lookup in a well-formed tree makes at most `2 * t` comparisons per level, under every
oracle. -/
theorem countQueries_lookupQ_le (h : IsWF t tr) (k : α) :
    (lookupQ k tr).countQueries oracle ≤ 2 * t * tr.height :=
  le_mul_height_of_scan (by have := h.two_le; omega) (countQueries_lookupQ_leaf oracle k)
    (fun first rest _ hB => countQueries_lookupQ_node_le oracle k first rest hB)
    h.rootKeys_le h.occupied_of_mem_children

/-- The membership test in a well-formed tree makes at most `2 * t` comparisons per level,
under every oracle. -/
theorem countQueries_containsQ_le (h : IsWF t tr) (k : α) :
    (containsQ k tr).countQueries oracle ≤ 2 * t * tr.height := by
  rw [countQueries_containsQ]
  exact countQueries_lookupQ_le oracle h k

/-- Predecessor search in a well-formed tree makes at most `2 * t` comparisons per level,
under every oracle. -/
theorem countQueries_predQ_le (h : IsWF t tr) (k : α) :
    (predQ k tr).countQueries oracle ≤ 2 * t * tr.height :=
  le_mul_height_of_scan (by have := h.two_le; omega) (countQueries_predQ_leaf oracle k)
    (fun first rest _ hB => countQueries_predQ_node_le oracle k first rest hB)
    h.rootKeys_le h.occupied_of_mem_children

/-- Successor search in a well-formed tree makes at most `2 * t` comparisons per level, under
every oracle. -/
theorem countQueries_succQ_le (h : IsWF t tr) (k : α) :
    (succQ k tr).countQueries oracle ≤ 2 * t * tr.height :=
  le_mul_height_of_scan (by have := h.two_le; omega) (countQueries_succQ_leaf oracle k)
    (fun first rest _ hB => countQueries_succQ_node_le oracle k first rest hB)
    h.rootKeys_le h.occupied_of_mem_children

/-- Rank in a well-formed tree makes at most `2 * t` comparisons per level, under every
oracle. -/
theorem countQueries_rankQ_le (h : IsWF t tr) (k : α) :
    (rankQ k tr).countQueries oracle ≤ 2 * t * tr.height :=
  le_mul_height_of_scan (by have := h.two_le; omega) (countQueries_rankQ_leaf oracle k)
    (fun first rest _ hB => countQueries_rankQ_node_le oracle k first rest hB)
    h.rootKeys_le h.occupied_of_mem_children

/-- Lookup in a well-formed tree makes logarithmically many comparisons. -/
theorem countQueries_lookupQ_le_log (h : IsWF t tr) (k : α) :
    (lookupQ k tr).countQueries oracle ≤ 2 * t * (Nat.log t ((tr.size + 1) / 2) + 1) :=
  (countQueries_lookupQ_le oracle h k).trans (Nat.mul_le_mul_left _ h.height_le_log)

/-- The membership test in a well-formed tree makes logarithmically many comparisons. -/
theorem countQueries_containsQ_le_log (h : IsWF t tr) (k : α) :
    (containsQ k tr).countQueries oracle ≤ 2 * t * (Nat.log t ((tr.size + 1) / 2) + 1) :=
  (countQueries_containsQ_le oracle h k).trans (Nat.mul_le_mul_left _ h.height_le_log)

/-- Predecessor search in a well-formed tree makes logarithmically many comparisons. -/
theorem countQueries_predQ_le_log (h : IsWF t tr) (k : α) :
    (predQ k tr).countQueries oracle ≤ 2 * t * (Nat.log t ((tr.size + 1) / 2) + 1) :=
  (countQueries_predQ_le oracle h k).trans (Nat.mul_le_mul_left _ h.height_le_log)

/-- Successor search in a well-formed tree makes logarithmically many comparisons. -/
theorem countQueries_succQ_le_log (h : IsWF t tr) (k : α) :
    (succQ k tr).countQueries oracle ≤ 2 * t * (Nat.log t ((tr.size + 1) / 2) + 1) :=
  (countQueries_succQ_le oracle h k).trans (Nat.mul_le_mul_left _ h.height_le_log)

/-- Rank in a well-formed tree makes logarithmically many comparisons. -/
theorem countQueries_rankQ_le_log (h : IsWF t tr) (k : α) :
    (rankQ k tr).countQueries oracle ≤ 2 * t * (Nat.log t ((tr.size + 1) / 2) + 1) :=
  (countQueries_rankQ_le oracle h k).trans (Nat.mul_le_mul_left _ h.height_le_log)

end Bounds

end Comparisons

/-! ### Upper bounds over all oracles -/

section UpperBounds

variable {α β : Type} [LinearOrder α] {t : ℕ}

/-- A well-formed tree of minimum degree `t` and a query key: the inputs of the bounded
point queries. -/
abbrev WFInput (α β : Type) [LinearOrder α] (t : ℕ) := {p : BTree α β × α // IsWF t p.1}

/-- Lookup makes at most `2 * t` comparisons at each of at most `height` nodes. -/
theorem lookupQ_upperBound :
    UpperBound (fun p : WFInput α β t => lookupQ p.val.2 p.val.1) (fun p => p.val.1.height)
      (fun h => 2 * t * h) :=
  UpperBound.of_pointwise (fun _ _ h => Nat.mul_le_mul_left _ h)
    fun oracle p => countQueries_lookupQ_le oracle p.property p.val.2

/-- The membership test makes at most `2 * t` comparisons at each of at most `height` nodes. -/
theorem containsQ_upperBound :
    UpperBound (fun p : WFInput α β t => containsQ p.val.2 p.val.1) (fun p => p.val.1.height)
      (fun h => 2 * t * h) :=
  UpperBound.of_pointwise (fun _ _ h => Nat.mul_le_mul_left _ h)
    fun oracle p => countQueries_containsQ_le oracle p.property p.val.2

/-- Predecessor search makes at most `2 * t` comparisons at each of at most `height` nodes. -/
theorem predQ_upperBound :
    UpperBound (fun p : WFInput α β t => predQ p.val.2 p.val.1) (fun p => p.val.1.height)
      (fun h => 2 * t * h) :=
  UpperBound.of_pointwise (fun _ _ h => Nat.mul_le_mul_left _ h)
    fun oracle p => countQueries_predQ_le oracle p.property p.val.2

/-- Successor search makes at most `2 * t` comparisons at each of at most `height` nodes. -/
theorem succQ_upperBound :
    UpperBound (fun p : WFInput α β t => succQ p.val.2 p.val.1) (fun p => p.val.1.height)
      (fun h => 2 * t * h) :=
  UpperBound.of_pointwise (fun _ _ h => Nat.mul_le_mul_left _ h)
    fun oracle p => countQueries_succQ_le oracle p.property p.val.2

/-- Rank makes at most `2 * t` comparisons at each of at most `height` nodes. -/
theorem rankQ_upperBound :
    UpperBound (fun p : WFInput α β t => rankQ p.val.2 p.val.1) (fun p => p.val.1.height)
      (fun h => 2 * t * h) :=
  UpperBound.of_pointwise (fun _ _ h => Nat.mul_le_mul_left _ h)
    fun oracle p => countQueries_rankQ_le oracle p.property p.val.2

end UpperBounds

end Cslib.DataStructure.BTree
