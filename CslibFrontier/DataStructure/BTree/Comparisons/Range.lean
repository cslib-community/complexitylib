/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.BTree.Comparisons.Query
public import CslibFrontier.DataStructure.BTree.Range

/-!
# Comparison cost of B-tree closed-interval queries

`rangeQ` instantiates `rangeM` in CSLib's query-complexity framework, at `FreeM (LEQuery α)` with
the comparison query `LEQuery.ask` and the trivial `visit := pure ()`. `eval_rangeQ` identifies
its value under `orderOracle` with `range`, through the transfer lemma
`Cslib.IsMonadHom.map_rangeM`.

The scan of a node compares each separator it reaches with both bounds, so one visited node can
cost `2 * (2 * t - 1)` comparisons: the per-node bound of `2 * t` behind the point-query bounds
fails, and the node-visit bound of `time_rangeT` cannot simply be multiplied by it. The count is
bounded instead by charging two comparisons to every returned entry and the rest to the two
boundary paths. `countQueries_rangeQ_of_occupied` proves at most `4 * t * height + 2 * k`
comparisons, where `k` is the length of the output, on any tree with sorted entries, at most
`2 * t - 1` root keys and children occupied for some `t > 0`, through three auxiliary bounds by
recursion on the tree:

* a subtree whose entries all lie in the interval costs two comparisons per returned entry;
* a subtree whose keys are all at least `lo` costs at most two more per level, for the
  separator above `hi` that stops each scan on the path towards `hi`;
* a subtree whose keys are all at most `hi` costs at most `2 * (2 * t - 1)` more per level, for
  the separators below `lo` on the path towards `lo`.

`countQueries_rangeQ_le` restates the bound on well-formed trees as
`2 * t * (2 * height + k)`, and `countQueries_rangeQ_le_log` composes it with
`IsWF.height_le_log`. The bounds are stated at the order's oracle only: under another oracle
the output is not the output under `≤`, so a bound in its length is not meaningful.

## Main definitions

* `rangeQ`: B-tree closed-interval query counting comparisons.

## Main results

* `countQueries_rangeQ_le`: the number of comparisons made by `rangeQ` is at most
  `2 * t * (2 * tr.height + (range lo hi tr).length)`.
* `eval_rangeQ`: the value of `rangeQ` evaluated at the order oracle matches `range`.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Chapter 18][CLRS2009]

Ported from cslib-community/EpsilonEridani PR #39 at commit 9425389c8.
-/

public section

open Cslib (FreeM)
open Cslib.Query (LEQuery)

namespace Cslib.DataStructure.BTree

section Comparisons

variable {α β : Type} {t : ℕ} {tr : BTree α β}

/-- Closed-interval query, issuing one query per key comparison. -/
def rangeQ (lo hi : α) (tr : BTree α β) : FreeM (LEQuery α) (List (α × β)) :=
  rangeM LEQuery.ask (pure ()) lo hi tr

/-- `rangeQ` is `rangeM` with the comparison query and free visits. -/
theorem rangeQ_def (lo hi : α) : rangeQ lo hi tr = rangeM LEQuery.ask (pure ()) lo hi tr := (rfl)

/-- A per-level charge `m` covers two comparisons per root key and the levels below the root. -/
private theorem two_mul_rootKeys_add_le {m : ℕ} (c : BTree α β) (hr : 2 * c.rootKeys ≤ m) :
    2 * c.rootKeys + m * (c.height - 1) ≤ m * c.height := by
  cases c with
  | leaf => simp
  | node first rest =>
    have := height_first_succ_le (first := first) (rest := rest)
    cases hh : (node first rest).height with
    | zero => omega
    | succ h =>
      rw [Nat.add_sub_cancel, Nat.mul_succ]
      omega

/-- A per-level charge on the first child fits below the root of its node. -/
private theorem mul_height_le_mul_height_node_sub_one (m : ℕ) (first : BTree α β)
    (rest : List (α × β × BTree α β)) :
    m * first.height ≤ m * ((node first rest).height - 1) :=
  Nat.mul_le_mul_left m (by have := height_first_succ_le (first := first) (rest := rest); omega)

/-- A per-level charge below the root of the node without its first child and separator fits
below the root of the original node. -/
private theorem mul_height_node_sub_one_le (m : ℕ) (first : BTree α β) (k : α) (v : β)
    (c : BTree α β) (rest : List (α × β × BTree α β)) :
    m * ((node c rest).height - 1) ≤ m * ((node first ((k, v, c) :: rest)).height - 1) :=
  Nat.mul_le_mul_left m
    (Nat.sub_le_sub_right (height_node_le_height_node_cons (first := first) (k := k) (v := v)) 1)

variable [LinearOrder α]

/-- Under the order's oracle, `rangeQ` evaluates to `range`. -/
@[simp] theorem eval_rangeQ (lo hi : α) : (rangeQ lo hi tr).eval orderOracle = range lo hi tr := by
  simpa [range_def, rangeQ] using
    Id.ext_iff.1
      ((FreeM.isMonadHom_pure_eval orderOracle).map_rangeM LEQuery.ask (pure ()) lo hi tr)

/-- The empty tree costs no comparison. -/
@[simp] theorem countQueries_rangeQ_leaf (lo hi : α) :
    (rangeQ lo hi (.leaf : BTree α β)).countQueries orderOracle = 0 := by
  simp [rangeQ, rangeM_leaf]

/-- A node without keys costs what its only child costs. -/
@[simp] theorem countQueries_rangeQ_node_nil (lo hi : α) (first : BTree α β) :
    (rangeQ lo hi (.node first [])).countQueries orderOracle =
      (rangeQ lo hi first).countQueries orderOracle := by
  simp [rangeQ, rangeM_node, rangeRestM_nil]

/-- The first separator is compared with both bounds; the child before it is searched when the
separator is at least `lo`, and the remaining triples are scanned, as the node without its first
child and separator, when the separator is at most `hi`. -/
@[simp] theorem countQueries_rangeQ_node_cons (lo hi k : α) (v : β) (first c : BTree α β)
    (rest : List (α × β × BTree α β)) :
    (rangeQ lo hi (.node first ((k, v, c) :: rest))).countQueries orderOracle =
      2 + (if lo ≤ k then (rangeQ lo hi first).countQueries orderOracle else 0) +
        (if k ≤ hi then (rangeQ lo hi (.node c rest)).countQueries orderOracle else 0) := by
  by_cases hlo : lo ≤ k <;> by_cases hhi : k ≤ hi <;>
    simp [rangeQ, rangeM_node, rangeRestM_cons, hlo, hhi] <;> omega

/-! ### Auxiliary bounds -/

variable {lo hi : α}

/-- A query whose interval contains every entry costs two comparisons per entry returned. -/
private theorem countQueries_rangeQ_le_of_forall_mem {lo hi : α} {tr : BTree α β}
    (hs : tr.toList.IsSortedAssoc) (hin : ∀ p ∈ tr.toList, lo ≤ p.1 ∧ p.1 ≤ hi) :
    (rangeQ lo hi tr).countQueries orderOracle ≤ 2 * (range lo hi tr).length := by
  match tr with
  | .leaf => simp
  | .node first [] =>
    have := countQueries_rangeQ_le_of_forall_mem (by simpa using hs)
      (fun p hp => hin p (by simpa using hp))
    simpa using this
  | .node first ((k, v, c) :: rest) =>
    obtain ⟨hsf, hsn, -, -⟩ := isSortedAssoc_toList_node_cons_iff.1 hs
    have hk := hin (k, v) (mem_toList_node_cons.2 (Or.inr (Or.inl rfl)))
    have h₁ := countQueries_rangeQ_le_of_forall_mem hsf
      (fun p hp => hin p (mem_toList_node_cons.2 (Or.inl hp)))
    have h₂ := countQueries_rangeQ_le_of_forall_mem hsn
      (fun p hp => hin p (mem_toList_node_cons.2 (Or.inr (Or.inr hp))))
    rw [countQueries_rangeQ_node_cons, length_range_node_cons lo hi]
    simp only [hk.1, hk.2, ↓reduceIte]
    omega
termination_by sizeOf tr

/-- A query on a tree whose keys are all at least `lo` costs at most two comparisons per level
beyond two per entry returned: the separator above `hi` that stops the scan on the path towards
`hi`. -/
private theorem countQueries_rangeQ_le_of_forall_lo_le {lo hi : α} {tr : BTree α β}
    (hs : tr.toList.IsSortedAssoc) (hlo : ∀ p ∈ tr.toList, lo ≤ p.1) :
    (rangeQ lo hi tr).countQueries orderOracle ≤ 2 * tr.height + 2 * (range lo hi tr).length := by
  match tr with
  | .leaf => simp
  | .node first [] =>
    have ih := countQueries_rangeQ_le_of_forall_lo_le (hi := hi) (by simpa using hs)
      (fun p hp => hlo p (by simpa using hp))
    have e := height_first_succ_le (first := first) (rest := [])
    rw [countQueries_rangeQ_node_nil, range_node_nil]
    omega
  | .node first ((k, v, c) :: rest) =>
    obtain ⟨hsf, hsn, hlt, -⟩ := isSortedAssoc_toList_node_cons_iff.1 hs
    have hk : lo ≤ k := hlo (k, v) (mem_toList_node_cons.2 (Or.inr (Or.inl rfl)))
    have e₁ := height_first_succ_le (first := first) (rest := (k, v, c) :: rest)
    have e₂ := height_node_le_height_node_cons (first := first) (k := k) (v := v) (c := c)
      (rest := rest)
    rw [countQueries_rangeQ_node_cons, length_range_node_cons lo hi]
    by_cases hhi : k ≤ hi
    · have h₁ := countQueries_rangeQ_le_of_forall_mem hsf
        (fun p hp => ⟨hlo p (mem_toList_node_cons.2 (Or.inl hp)), ((hlt p hp).trans_le hhi).le⟩)
      have h₂ := countQueries_rangeQ_le_of_forall_lo_le (hi := hi) hsn
        (fun p hp => hlo p (mem_toList_node_cons.2 (Or.inr (Or.inr hp))))
      simp only [hk, hhi, ↓reduceIte]
      omega
    · have h₁ := countQueries_rangeQ_le_of_forall_lo_le (hi := hi) hsf
        (fun p hp => hlo p (mem_toList_node_cons.2 (Or.inl hp)))
      simp only [hk, hhi, ↓reduceIte]
      omega
termination_by sizeOf tr

/-- A query on a tree whose keys are all at most `hi` costs, beyond two comparisons per entry
returned, two per root key and at most `2 * (2 * t - 1)` per level below the root: the
separators below `lo` on the path towards `lo`. -/
private theorem countQueries_rangeQ_le_of_forall_le_hi {lo hi : α} {tr : BTree α β}
    (hc : ∀ c ∈ tr.children, Occupied t c) (hs : tr.toList.IsSortedAssoc)
    (hhi : ∀ p ∈ tr.toList, p.1 ≤ hi) :
    (rangeQ lo hi tr).countQueries orderOracle ≤
      2 * tr.rootKeys + (4 * t - 2) * (tr.height - 1) + 2 * (range lo hi tr).length := by
  match tr with
  | .leaf => simp
  | .node first [] =>
    have hfirst : Occupied t first := hc first (by simp)
    have ih := countQueries_rangeQ_le_of_forall_le_hi (lo := lo)
      (fun c h => hfirst.of_mem_children h) (by simpa using hs)
      (fun p hp => hhi p (by simpa using hp))
    have e := height_first_succ_le (first := first) (rest := [])
    have h₁ := two_mul_rootKeys_add_le first (m := 4 * t - 2)
      (by have := hfirst.rootKeys_le; omega)
    have h₂ := mul_height_le_mul_height_node_sub_one (4 * t - 2) first []
    rw [countQueries_rangeQ_node_nil, range_node_nil]
    omega
  | .node first ((k, v, c) :: rest) =>
    obtain ⟨hsf, hsn, -, hgt⟩ := isSortedAssoc_toList_node_cons_iff.1 hs
    obtain ⟨hfirst, hcf, hcn⟩ := occupied_children_node_cons hc
    have hk : k ≤ hi := hhi (k, v) (mem_toList_node_cons.2 (Or.inr (Or.inl rfl)))
    have e₁ := height_first_succ_le (first := first) (rest := (k, v, c) :: rest)
    have e₂ := height_node_le_height_node_cons (first := first) (k := k) (v := v) (c := c)
      (rest := rest)
    rw [countQueries_rangeQ_node_cons, length_range_node_cons lo hi]
    simp only [rootKeys_node, List.length_cons]
    by_cases hlo : lo ≤ k
    · have h₁ := countQueries_rangeQ_le_of_forall_le_hi (lo := lo) hcf hsf
        (fun p hp => hhi p (mem_toList_node_cons.2 (Or.inl hp)))
      have h₂ := countQueries_rangeQ_le_of_forall_mem hsn
        (fun p hp => ⟨hlo.trans (hgt p hp).le,
          hhi p (mem_toList_node_cons.2 (Or.inr (Or.inr hp)))⟩)
      have h₃ := two_mul_rootKeys_add_le first (m := 4 * t - 2)
        (by have := hfirst.rootKeys_le; omega)
      have h₄ := mul_height_le_mul_height_node_sub_one (4 * t - 2) first ((k, v, c) :: rest)
      simp only [hk, hlo, ↓reduceIte]
      omega
    · have h₂ := countQueries_rangeQ_le_of_forall_le_hi (lo := lo) hcn hsn
        (fun p hp => hhi p (mem_toList_node_cons.2 (Or.inr (Or.inr hp))))
      have h₄ := mul_height_node_sub_one_le (4 * t - 2) first k v c rest
      simp only [rootKeys_node] at h₂
      simp only [hk, hlo, ↓reduceIte]
      omega
termination_by sizeOf tr

/-- A query on a tree with sorted entries and occupied children costs, beyond two comparisons per
entry returned, two per root key and at most `4 * t` per level below the root. -/
private theorem countQueries_rangeQ_le_rootKeys {lo hi : α} {tr : BTree α β} (ht : 0 < t)
    (hc : ∀ c ∈ tr.children, Occupied t c) (hs : tr.toList.IsSortedAssoc) :
    (rangeQ lo hi tr).countQueries orderOracle ≤
      2 * tr.rootKeys + 4 * t * (tr.height - 1) + 2 * (range lo hi tr).length := by
  match tr with
  | .leaf => simp
  | .node first [] =>
    have hfirst : Occupied t first := hc first (by simp)
    have ih := countQueries_rangeQ_le_rootKeys (lo := lo) (hi := hi) ht
      (fun c h => hfirst.of_mem_children h) (by simpa using hs)
    have e := height_first_succ_le (first := first) (rest := [])
    have h₁ := two_mul_rootKeys_add_le first (m := 4 * t) (by have := hfirst.rootKeys_le; omega)
    have h₂ := mul_height_le_mul_height_node_sub_one (4 * t) first []
    rw [countQueries_rangeQ_node_nil, range_node_nil]
    omega
  | .node first ((k, v, c) :: rest) =>
    obtain ⟨hsf, hsn, hlt, hgt⟩ := isSortedAssoc_toList_node_cons_iff.1 hs
    obtain ⟨hfirst, hcf, hcn⟩ := occupied_children_node_cons hc
    have e₁ := height_first_succ_le (first := first) (rest := (k, v, c) :: rest)
    have e₂ := height_node_le_height_node_cons (first := first) (k := k) (v := v) (c := c)
      (rest := rest)
    rw [countQueries_rangeQ_node_cons, length_range_node_cons lo hi]
    simp only [rootKeys_node, List.length_cons]
    by_cases hlo : lo ≤ k <;> by_cases hhi : k ≤ hi
    · have h₁ := countQueries_rangeQ_le_of_forall_le_hi (lo := lo) hcf hsf
        (fun p hp => ((hlt p hp).trans_le hhi).le)
      have h₂ := countQueries_rangeQ_le_of_forall_lo_le (hi := hi) hsn
        (fun p hp => (hlo.trans_lt (hgt p hp)).le)
      have h₃ := two_mul_rootKeys_add_le first (m := 4 * t - 2)
        (by have := hfirst.rootKeys_le; omega)
      have h₄ := mul_height_le_mul_height_node_sub_one (4 * t - 2) first ((k, v, c) :: rest)
      have h₅ : (4 * t - 2) * ((node first ((k, v, c) :: rest)).height - 1) +
          2 * ((node first ((k, v, c) :: rest)).height - 1) ≤
          4 * t * ((node first ((k, v, c) :: rest)).height - 1) := by
        rw [← Nat.add_mul]
        exact Nat.mul_le_mul_right _ (by omega)
      simp only [hlo, hhi, ↓reduceIte]
      omega
    · have h₁ := countQueries_rangeQ_le_rootKeys (lo := lo) (hi := hi) ht hcf hsf
      have h₃ := two_mul_rootKeys_add_le first (m := 4 * t)
        (by have := hfirst.rootKeys_le; omega)
      have h₄ := mul_height_le_mul_height_node_sub_one (4 * t) first ((k, v, c) :: rest)
      simp only [hlo, hhi, ↓reduceIte]
      omega
    · have h₂ := countQueries_rangeQ_le_rootKeys (lo := lo) (hi := hi) ht hcn hsn
      have h₄ := mul_height_node_sub_one_le (4 * t) first k v c rest
      simp only [rootKeys_node] at h₂
      simp only [hlo, hhi, ↓reduceIte]
      omega
    · simp only [hlo, hhi, ↓reduceIte]
      omega
termination_by sizeOf tr

/-! ### Comparison bounds -/

/-- A closed-interval query makes at most `4 * t * height + 2 * k` comparisons, where `k` is the
number of entries it returns, on any tree with sorted entries, at most `2 * t - 1` root keys and
children occupied for some `t > 0`. Each returned entry costs two comparisons; at each level,
the path towards `lo` costs at most `2 * (2 * t - 1)` more and the path towards `hi` at most
two. -/
theorem countQueries_rangeQ_of_occupied {tr : BTree α β} (ht : 0 < t)
    (hr : tr.rootKeys ≤ 2 * t - 1) (hc : ∀ c ∈ tr.children, Occupied t c)
    (hs : tr.toList.IsSortedAssoc) :
    (rangeQ lo hi tr).countQueries orderOracle ≤
      4 * t * tr.height + 2 * (range lo hi tr).length := by
  have := countQueries_rangeQ_le_rootKeys (lo := lo) (hi := hi) ht hc hs
  have := two_mul_rootKeys_add_le tr (m := 4 * t) (by omega)
  omega

/-- A closed-interval query on a well-formed tree makes at most `2 * t * (2 * height + k)`
comparisons, where `k` is the number of entries it returns: the node-visit bound `2 * height + k`
of `time_rangeT` times `2 * t`. A single node can cost more than `2 * t` comparisons, so this is
a consequence of `countQueries_rangeQ_of_occupied`, not a per-node bound. -/
theorem countQueries_rangeQ_le (h : IsWF t tr) (lo hi : α) :
    (rangeQ lo hi tr).countQueries orderOracle ≤
      2 * t * (2 * tr.height + (range lo hi tr).length) := by
  have := countQueries_rangeQ_of_occupied (lo := lo) (hi := hi) (by have := h.two_le; omega)
    h.rootKeys_le h.occupied_of_mem_children h.sorted
  have ht : 2 ≤ 2 * t := by have := h.two_le; omega
  have := Nat.mul_le_mul_right (range lo hi tr).length ht
  calc _ ≤ 4 * t * tr.height + 2 * t * (range lo hi tr).length := by omega
    _ = 2 * t * (2 * tr.height + (range lo hi tr).length) := by grind

/-- A closed-interval query on a well-formed tree makes logarithmically many comparisons beyond
`2 * t` per entry it returns. -/
theorem countQueries_rangeQ_le_log (h : IsWF t tr) (lo hi : α) :
    (rangeQ lo hi tr).countQueries orderOracle ≤
      2 * t * (2 * (Nat.log t ((tr.size + 1) / 2) + 1) + (range lo hi tr).length) :=
  (countQueries_rangeQ_le h lo hi).trans
    (Nat.mul_le_mul_left _ (by have := h.height_le_log; omega))

end Comparisons

end Cslib.DataStructure.BTree
