/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.BTree.Cost.Query
public import CslibFrontier.DataStructure.BTree.Range

/-!
# Node-visit cost of B-tree closed-interval queries

`rangeT` instantiates `rangeM` at `TimeM ℕ` with the free comparator `leT` and `visit := tick 1`,
in the node-visit model of `Cslib.DataStructure.BTree.Cost.Query`.

A visited node either returns one of its own keys or has every key outside the interval; in the
second case the keys that can lie below it straddle `lo` or `hi`, and at each depth at most one
node straddles each bound. The proof makes this precise with three private bounds, by recursion
on the tree:

* a subtree whose entries all lie in the interval is visited at most once per returned entry,
  because every occupied node has a key when `2 ≤ t`;
* a subtree whose keys are all at least `lo`, or all at most `hi`, is visited at most
  `height + k` times: only the path towards the other bound is unpaid;
* at the node where `lo` and `hi` part ways, the child towards `lo` has all its keys at most `hi`
  and the remaining triples have all their keys at least `lo`.

Occupancy is needed: a chain of keyless nodes inside the interval would be visited without
contributing output.

## Main definitions

* `rangeT`: the instrumented closed-interval query.

## Main results

* `ret_rangeT`: the value of `rangeT` is `range`.
* `time_rangeT_of_occupied`: at most `2 * height + k` visits, where `k` is the length of the
  output, on a tree with sorted entries and occupied children.
* `time_rangeT`, `time_rangeT_le_log`: the bound on well-formed trees, and with
  `IsWF.height_le_log`.

Ported from `cslib-community/EpsilonEridani` at commit `1966ab476`:
[EpsilonEridani/Algorithms/Lean/BTree/Cost/Range.lean](https://github.com/cslib-community/EpsilonEridani/blob/1966ab476f5db00425c83e19857fd38ba01143c4/EpsilonEridani/Algorithms/Lean/BTree/Cost/Range.lean).
-/

public section

open Cslib.Algorithms.Lean (TimeM)
open Cslib.Algorithms.Lean.TimeM (tick)

namespace Cslib.DataStructure.BTree

section NodeVisits

variable {α β : Type} [LinearOrder α] {t : ℕ} {tr : BTree α β}

/-- Closed-interval query, charging one tick per node visited. -/
def rangeT (lo hi : α) (tr : BTree α β) : TimeM ℕ (List (α × β)) :=
  rangeM leT (tick 1) lo hi tr

/-- `rangeT` is `rangeM` with the free comparator and one tick per visit. -/
theorem rangeT_def (lo hi : α) : rangeT lo hi tr = rangeM leT (tick 1) lo hi tr := (rfl)

/-- The value of `rangeT` is `range`. -/
@[simp] theorem ret_rangeT (lo hi : α) : (rangeT lo hi tr).ret = range lo hi tr := by
  simpa only [range_def, rangeT, leI, Id.run_pure, TimeM.ret_pure, TimeM.ret_tick] using
    Id.ext_iff.1 (TimeM.isMonadHom_pure_ret.map_rangeM leT (tick 1) lo hi tr)

/-- The empty tree is not visited. -/
@[simp] theorem time_rangeT_leaf (lo hi : α) : (rangeT lo hi (.leaf : BTree α β)).time = 0 := by
  simp [rangeT, rangeM_leaf]

/-- A node without keys is visited once before its only child. -/
@[simp] theorem time_rangeT_node_nil (lo hi : α) (first : BTree α β) :
    (rangeT lo hi (.node first [])).time = (rangeT lo hi first).time + 1 := by
  simp [rangeT, rangeM_node, rangeRestM_nil]
  omega

/-- At the first separator, the child before it is entered when the separator is at least `lo`,
and the remaining triples are scanned, as the node without its first child and separator, when
the separator is at most `hi`. That node accounts for the single visit of the original node. -/
@[simp] theorem time_rangeT_node_cons (lo hi k : α) (v : β) (first c : BTree α β)
    (rest : List (Triple α β)) :
    (rangeT lo hi (.node first ((k, v, c) :: rest))).time =
      (if lo ≤ k then (rangeT lo hi first).time else 0) +
        (if k ≤ hi then (rangeT lo hi (.node c rest)).time else 1) := by
  by_cases hlo : lo ≤ k <;> by_cases hhi : k ≤ hi <;>
    simp [rangeT, rangeM_node, rangeRestM_cons, hlo, hhi] <;> omega

/-! ### Auxiliary bounds -/

variable {lo hi : α}

/-- A query whose interval contains every entry visits each node once and returns at least one
entry per occupied node. The root's keys pay for its own visit and for the visit it causes in
the node without its first child. -/
private theorem time_rangeT_add_rootKeys_le {lo hi : α} {tr : BTree α β} (ht : 2 ≤ t)
    (hc : ∀ c ∈ tr.children, Occupied t c) (hs : tr.toList.IsSortedAssoc)
    (hin : ∀ p ∈ tr.toList, lo ≤ p.1 ∧ p.1 ≤ hi) :
    (rangeT lo hi tr).time + tr.rootKeys ≤ (range lo hi tr).length + 1 := by
  have occ {c : BTree α β} (ho : Occupied t c)
      (h : (rangeT lo hi c).time + c.rootKeys ≤ (range lo hi c).length + 1) :
      (rangeT lo hi c).time ≤ (range lo hi c).length := by
    cases c with
    | leaf => simp
    | node _ _ =>
      have := ho.one_le_rootKeys ht (by simp)
      omega
  match tr with
  | .leaf => simp
  | .node first [] =>
    have hfirst : Occupied t first := hc first (by simp)
    have ih := time_rangeT_add_rootKeys_le ht (fun c h => hfirst.of_mem_children h)
      (by simpa using hs) (fun p hp => hin p (by simpa using hp))
    have := occ hfirst ih
    simp [time_rangeT_node_nil, rootKeys]
    omega
  | .node first ((k, v, c) :: rest) =>
    obtain ⟨hsf, hsn, -, -⟩ := isSortedAssoc_toList_node_cons_iff.1 hs
    obtain ⟨hfirst, hcf, hcn⟩ := occupied_children_node_cons hc
    have hk := hin (k, v) (mem_toList_node_cons.2 (Or.inr (Or.inl rfl)))
    have ih₁ := time_rangeT_add_rootKeys_le ht hcf hsf
      (fun p hp => hin p (mem_toList_node_cons.2 (Or.inl hp)))
    have ih₂ := time_rangeT_add_rootKeys_le ht hcn hsn
      (fun p hp => hin p (mem_toList_node_cons.2 (Or.inr (Or.inr hp))))
    have := occ hfirst ih₁
    simp only [rootKeys, List.length_cons] at ih₂ ⊢
    rw [time_rangeT_node_cons, length_range_node_cons lo hi]
    simp only [hk.1, hk.2, ↓reduceIte]
    omega
termination_by sizeOf tr

/-- An occupied tree whose entries all lie in the interval is visited at most once per entry
returned. -/
private theorem time_rangeT_le_of_forall_mem (ht : 2 ≤ t) (ho : Occupied t tr)
    (hs : tr.toList.IsSortedAssoc) (hin : ∀ p ∈ tr.toList, lo ≤ p.1 ∧ p.1 ≤ hi) :
    (rangeT lo hi tr).time ≤ (range lo hi tr).length := by
  have h := time_rangeT_add_rootKeys_le ht (fun c hc => ho.of_mem_children hc) hs hin
  cases tr with
  | leaf => simp
  | node _ _ =>
    have := ho.one_le_rootKeys ht (by simp)
    omega

/-- A query on a tree whose keys are all at least `lo` pays at most one unproductive visit per
level, on the path towards `hi`. -/
private theorem time_rangeT_le_of_forall_lo_le {lo hi : α} {tr : BTree α β} (ht : 2 ≤ t)
    (hc : ∀ c ∈ tr.children, Occupied t c) (hs : tr.toList.IsSortedAssoc)
    (hlo : ∀ p ∈ tr.toList, lo ≤ p.1) :
    (rangeT lo hi tr).time ≤ tr.height + (range lo hi tr).length := by
  match tr with
  | .leaf => simp
  | .node first [] =>
    have hfirst : Occupied t first := hc first (by simp)
    have ih := time_rangeT_le_of_forall_lo_le (hi := hi) ht
      (fun c h => hfirst.of_mem_children h) (by simpa using hs)
      (fun p hp => hlo p (by simpa using hp))
    have e := height_first_succ_le (first := first) (rest := [])
    rw [time_rangeT_node_nil, range_node_nil]
    omega
  | .node first ((k, v, c) :: rest) =>
    obtain ⟨hsf, hsn, hlt, -⟩ := isSortedAssoc_toList_node_cons_iff.1 hs
    obtain ⟨hfirst, hcf, hcn⟩ := occupied_children_node_cons hc
    have hk : lo ≤ k := hlo (k, v) (mem_toList_node_cons.2 (Or.inr (Or.inl rfl)))
    have e₁ := height_first_succ_le (first := first) (rest := (k, v, c) :: rest)
    have e₂ := height_node_le_height_node_cons (first := first) (k := k) (v := v) (c := c)
      (rest := rest)
    rw [time_rangeT_node_cons, length_range_node_cons lo hi]
    by_cases hhi : k ≤ hi
    · have h₁ := time_rangeT_le_of_forall_mem ht hfirst hsf
        (fun p hp => ⟨hlo p (mem_toList_node_cons.2 (Or.inl hp)), ((hlt p hp).trans_le hhi).le⟩)
      have h₂ := time_rangeT_le_of_forall_lo_le (hi := hi) ht hcn hsn
        (fun p hp => hlo p (mem_toList_node_cons.2 (Or.inr (Or.inr hp))))
      simp only [hk, hhi, ↓reduceIte]
      omega
    · have h₁ := time_rangeT_le_of_forall_lo_le (hi := hi) ht hcf hsf
        (fun p hp => hlo p (mem_toList_node_cons.2 (Or.inl hp)))
      simp only [hk, hhi, ↓reduceIte]
      omega
termination_by sizeOf tr

/-- A query on a tree whose keys are all at most `hi` pays at most one unproductive visit per
level, on the path towards `lo`. -/
private theorem time_rangeT_le_of_forall_le_hi {lo hi : α} {tr : BTree α β} (ht : 2 ≤ t)
    (hc : ∀ c ∈ tr.children, Occupied t c) (hs : tr.toList.IsSortedAssoc)
    (hhi : ∀ p ∈ tr.toList, p.1 ≤ hi) :
    (rangeT lo hi tr).time ≤ tr.height + (range lo hi tr).length := by
  match tr with
  | .leaf => simp
  | .node first [] =>
    have hfirst : Occupied t first := hc first (by simp)
    have ih := time_rangeT_le_of_forall_le_hi (lo := lo) ht
      (fun c h => hfirst.of_mem_children h) (by simpa using hs)
      (fun p hp => hhi p (by simpa using hp))
    have e := height_first_succ_le (first := first) (rest := [])
    rw [time_rangeT_node_nil, range_node_nil]
    omega
  | .node first ((k, v, c) :: rest) =>
    obtain ⟨hsf, hsn, -, hgt⟩ := isSortedAssoc_toList_node_cons_iff.1 hs
    obtain ⟨-, hcf, hcn⟩ := occupied_children_node_cons hc
    have hk : k ≤ hi := hhi (k, v) (mem_toList_node_cons.2 (Or.inr (Or.inl rfl)))
    have e₁ := height_first_succ_le (first := first) (rest := (k, v, c) :: rest)
    have e₂ := height_node_le_height_node_cons (first := first) (k := k) (v := v) (c := c)
      (rest := rest)
    rw [time_rangeT_node_cons, length_range_node_cons lo hi]
    by_cases hlo : lo ≤ k
    · have h₁ := time_rangeT_le_of_forall_le_hi (lo := lo) ht hcf hsf
        (fun p hp => hhi p (mem_toList_node_cons.2 (Or.inl hp)))
      have h₂ := time_rangeT_add_rootKeys_le ht hcn hsn
        (fun p hp => ⟨hlo.trans (hgt p hp).le, hhi p (mem_toList_node_cons.2 (Or.inr (Or.inr hp)))⟩)
      simp only [rootKeys] at h₂
      simp only [hk, hlo, ↓reduceIte]
      omega
    · have h₂ := time_rangeT_le_of_forall_le_hi (lo := lo) ht hcn hsn
        (fun p hp => hhi p (mem_toList_node_cons.2 (Or.inr (Or.inr hp))))
      simp only [hk, hlo, ↓reduceIte]
      omega
termination_by sizeOf tr

/-! ### Node-visit bounds -/

/-- A closed-interval query visits at most `2 * height + k` nodes, where `k` is the number of
entries it returns, on any tree with sorted entries whose children are occupied for some `t ≥ 2`.
Below the node where `lo` and `hi` part ways, each of the two boundary paths pays at most one
unproductive visit per level. Neither balance nor the root's key count is needed. -/
theorem time_rangeT_of_occupied {lo hi : α} {tr : BTree α β} (ht : 2 ≤ t)
    (hc : ∀ c ∈ tr.children, Occupied t c) (hs : tr.toList.IsSortedAssoc) :
    (rangeT lo hi tr).time ≤ 2 * tr.height + (range lo hi tr).length := by
  match tr with
  | .leaf => simp
  | .node first [] =>
    have hfirst : Occupied t first := hc first (by simp)
    have ih := time_rangeT_of_occupied (lo := lo) (hi := hi) ht
      (fun c h => hfirst.of_mem_children h) (by simpa using hs)
    have e := height_first_succ_le (first := first) (rest := [])
    rw [time_rangeT_node_nil, range_node_nil]
    omega
  | .node first ((k, v, c) :: rest) =>
    obtain ⟨hsf, hsn, hlt, hgt⟩ := isSortedAssoc_toList_node_cons_iff.1 hs
    obtain ⟨-, hcf, hcn⟩ := occupied_children_node_cons hc
    have e₁ := height_first_succ_le (first := first) (rest := (k, v, c) :: rest)
    have e₂ := height_node_le_height_node_cons (first := first) (k := k) (v := v) (c := c)
      (rest := rest)
    rw [time_rangeT_node_cons, length_range_node_cons lo hi]
    by_cases hlo : lo ≤ k <;> by_cases hhi : k ≤ hi
    · have h₁ := time_rangeT_le_of_forall_le_hi (lo := lo) ht hcf hsf
        (fun p hp => ((hlt p hp).trans_le hhi).le)
      have h₂ := time_rangeT_le_of_forall_lo_le (hi := hi) ht hcn hsn
        (fun p hp => (hlo.trans_lt (hgt p hp)).le)
      simp only [hlo, hhi, ↓reduceIte]
      omega
    · have h₁ := time_rangeT_of_occupied (lo := lo) (hi := hi) ht hcf hsf
      simp only [hlo, hhi, ↓reduceIte]
      omega
    · have h₂ := time_rangeT_of_occupied (lo := lo) (hi := hi) ht hcn hsn
      simp only [hlo, hhi, ↓reduceIte]
      omega
    · simp only [hlo, hhi, ↓reduceIte]
      omega
termination_by sizeOf tr

/-- A closed-interval query on a well-formed tree visits at most `2 * height + k` nodes, where `k`
is the number of entries it returns. -/
theorem time_rangeT (h : IsWF t tr) (lo hi : α) :
    (rangeT lo hi tr).time ≤ 2 * tr.height + (range lo hi tr).length :=
  time_rangeT_of_occupied h.two_le h.occupied_of_mem_children h.sorted

/-- A closed-interval query on a well-formed tree visits logarithmically many nodes beyond one per
entry it returns. -/
theorem time_rangeT_le_log (h : IsWF t tr) (lo hi : α) :
    (rangeT lo hi tr).time ≤ 2 * (Nat.log t ((tr.size + 1) / 2) + 1) + (range lo hi tr).length :=
  (time_rangeT h lo hi).trans (by have := h.height_le_log; omega)

end NodeVisits

end Cslib.DataStructure.BTree
