/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module
-- upstream: candidate

public import Complexity.DataStructure.BTree.Basic
public import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.Group.Nat

/-!
# Size and height of classic B-trees

The three inequalities relating the size and height of a well-formed classic B-tree of minimum
degree `t`, after [CLRS2009], Chapter 18. They follow from the corresponding bounds for non-root
subtrees, `Occupied.pow_sub_one_le_size` and `Occupied.size_le`. These are structural facts about
the shape of a tree; they carry no cost content.

## Main results

* `IsWF.le_size`: a non-empty tree of height `h` has at least `2 * t ^ (h - 1) - 1` entries.
* `IsWF.size_le`: a tree of height `h` has at most `(2 * t) ^ h - 1` entries.
* `IsWF.height_le_log`: the height is at most `Nat.log t ((size + 1) / 2) + 1`, the bound of
  [CLRS2009], Theorem 18.1, with heights counted in nodes rather than edges.
* `Balanced.height_le_log`: the same bound from the shape alone, without key order.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Chapter 18][CLRS2009]

Ported from `cslib-community/EpsilonEridani` at commit `1966ab476`:
[EpsilonEridani/Algorithms/Lean/BTree/Height.lean](https://github.com/cslib-community/EpsilonEridani/blob/1966ab476f5db00425c83e19857fd38ba01143c4/EpsilonEridani/Algorithms/Lean/BTree/Height.lean).
-/

public section

namespace Cslib.DataStructure.BTree

variable {α : Type*} {β : Type*}

/-! ### Nodes -/

section Node

variable {first : BTree α β} {rest : List (Triple α β)}

/-- A node whose children each hold at least `n - 1` entries holds at least
`(rest.length + 1) * n - 1`. -/
theorem le_size_node {n : ℕ} (h₁ : n - 1 ≤ first.size) (h₂ : ∀ e ∈ rest, n - 1 ≤ e.child.size) :
    (rest.length + 1) * n - 1 ≤ (node first rest).size := by
  have hs :=
    (rest.map fun e => e.child.size).length_nsmul_le_sum (n - 1) (List.forall_mem_map.2 h₂)
  rw [List.length_map, Nat.nsmul_eq_mul] at hs
  rw [size_node]
  obtain _ | n := n
  · simp
  · rw [Nat.add_sub_cancel] at h₁ hs
    rw [Nat.add_mul, Nat.mul_add]
    omega

/-- A node whose children each hold at most `n - 1` entries, for positive `n`, holds at most
`(rest.length + 1) * n - 1`. -/
theorem size_node_le {n : ℕ} (hn : 0 < n) (h₁ : first.size ≤ n - 1)
    (h₂ : ∀ e ∈ rest, e.child.size ≤ n - 1) :
    (node first rest).size ≤ (rest.length + 1) * n - 1 := by
  have hs :=
    (rest.map fun e => e.child.size).sum_le_length_nsmul (n - 1) (List.forall_mem_map.2 h₂)
  rw [List.length_map, Nat.nsmul_eq_mul] at hs
  rw [size_node]
  obtain _ | n := n
  · omega
  · rw [Nat.add_sub_cancel] at h₁ hs
    rw [Nat.add_mul, Nat.mul_add]
    omega

end Node

/-! ### Bounds -/

variable {t : ℕ} {tr : BTree α β}

/-- A balanced occupied subtree of height `h` holds at least `t ^ h - 1` entries. -/
theorem Occupied.pow_sub_one_le_size (ho : Occupied t tr) (hb : Balanced tr) :
    t ^ tr.height - 1 ≤ tr.size := by
  induction tr with
  | leaf => simp
  | node first rest ih₁ ih₂ =>
    have hc : ∀ e : Triple α β, e ∈ rest → t ^ first.height - 1 ≤ e.child.size := fun e he =>
      hb.height_of_mem_rest he ▸ ih₂ e he (ho.of_mem_rest he) (hb.of_mem_rest he)
    refine le_trans ?_ (le_size_node (ih₁ ho.first hb.first) hc)
    rw [hb.height_node, Nat.pow_succ']
    exact Nat.sub_le_sub_right (Nat.mul_le_mul_right _ (by have := ho.le_length; omega)) 1

/-- A node with at most `2 * t - 1` keys, for positive `t`, whose children each satisfy the
upper bound of `Occupied.size_le` satisfies it too. -/
private theorem size_node_le_pow {first : BTree α β} {rest : List (Triple α β)}
    (ht : 0 < t) (hm : rest.length ≤ 2 * t - 1)
    (hc : ∀ c ∈ (node first rest).children, c.size ≤ (2 * t) ^ c.height - 1) :
    (node first rest).size ≤ (2 * t) ^ (node first rest).height - 1 := by
  have hpos := height_succ_le_of_mem_children (tr := node first rest) List.mem_cons_self
  obtain ⟨H, hH⟩ : ∃ H, (node first rest).height = H + 1 :=
    ⟨_, (Nat.sub_add_cancel (by omega)).symm⟩
  have hle : ∀ c ∈ (node first rest).children, c.size ≤ (2 * t) ^ H - 1 := fun c hc' =>
    (hc c hc').trans (Nat.sub_le_sub_right (Nat.pow_le_pow_right (by omega)
      (by have := height_succ_le_of_mem_children hc'; omega)) 1)
  rw [hH, Nat.pow_succ']
  exact (size_node_le (Nat.pow_pos (by omega)) (hle _ List.mem_cons_self) fun e he =>
    hle _ (List.mem_cons_of_mem _ (List.mem_map_of_mem he))).trans
      (Nat.sub_le_sub_right (Nat.mul_le_mul_right _ (by omega)) 1)

/-- An occupied subtree of height `h` holds at most `(2 * t) ^ h - 1` entries. -/
theorem Occupied.size_le (ho : Occupied t tr) : tr.size ≤ (2 * t) ^ tr.height - 1 := by
  induction tr with
  | leaf => simp
  | node first rest ih₁ ih₂ =>
    have hm := ho.length_le
    obtain rfl | ht := Nat.eq_zero_or_pos t
    · obtain rfl : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
      have h0 : ∀ n, (2 * 0) ^ n - 1 = 0 := fun n => by cases n <;> simp
      have hf := ih₁ ho.first
      rw [h0] at hf ⊢
      simpa [size_node] using hf
    · have ih : ∀ c ∈ (BTree.node first rest).children,
          Occupied t c → c.size ≤ (2 * t) ^ c.height - 1 := by
        simpa only [children_node, List.forall_mem_cons, List.forall_mem_map] using ⟨ih₁, ih₂⟩
      exact size_node_le_pow ht hm fun c hc => ih c hc (ho.of_mem_children hc)

/-- A non-empty balanced tree of height `h` with a key at the root and occupied children holds at
least `2 * t ^ (h - 1) - 1` entries. Only the shape matters, not the order of the keys. -/
theorem Balanced.le_size (hb : Balanced tr) (hk : tr ≠ .leaf → 1 ≤ tr.rootKeys)
    (ho : ∀ c ∈ tr.children, Occupied t c) (hne : tr ≠ .leaf) :
    2 * t ^ (tr.height - 1) - 1 ≤ tr.size := by
  cases tr with
  | leaf => exact absurd rfl hne
  | node first rest =>
    have hk := hk hne
    rw [rootKeys_node] at hk
    have hc : ∀ e : Triple α β, e ∈ rest → t ^ first.height - 1 ≤ e.child.size := fun e he =>
      hb.height_of_mem_rest he ▸
        (ho _ (List.mem_cons_of_mem _ (List.mem_map_of_mem he))).pow_sub_one_le_size
          (hb.of_mem_rest he)
    refine le_trans ?_
      (le_size_node ((ho first List.mem_cons_self).pow_sub_one_le_size hb.first) hc)
    rw [hb.height_node, Nat.add_sub_cancel]
    exact Nat.sub_le_sub_right (Nat.mul_le_mul_right _ (by omega)) 1

/-- The height of a balanced tree with a key at a non-empty root and occupied children is
logarithmic in its size, for `2 ≤ t`. Only the shape matters, not the order of the keys. -/
theorem Balanced.height_le_log (ht : 2 ≤ t) (hb : Balanced tr) (hk : tr ≠ .leaf → 1 ≤ tr.rootKeys)
    (ho : ∀ c ∈ tr.children, Occupied t c) : tr.height ≤ Nat.log t ((tr.size + 1) / 2) + 1 := by
  rcases eq_or_ne tr .leaf with rfl | hne
  · simp
  have hs := hb.le_size hk ho hne
  have hle : t ^ (tr.height - 1) ≤ (tr.size + 1) / 2 :=
    (Nat.le_div_iff_mul_le (by decide)).2 (by omega)
  have := Nat.le_log_of_pow_le (by omega) hle
  omega

variable [LinearOrder α]

/-- A non-empty well-formed tree of height `h` holds at least `2 * t ^ (h - 1) - 1` entries. -/
theorem IsWF.le_size (h : IsWF t tr) (hne : tr ≠ .leaf) :
    2 * t ^ (tr.height - 1) - 1 ≤ tr.size :=
  h.balanced.le_size h.rootKeys_pos h.occupied_of_mem_children hne

/-- A well-formed tree of height `h` holds at most `(2 * t) ^ h - 1` entries. -/
theorem IsWF.size_le (h : IsWF t tr) : tr.size ≤ (2 * t) ^ tr.height - 1 := by
  cases tr with
  | leaf => simp
  | node first rest =>
    exact size_node_le_pow (by have := h.two_le; omega) h.rootKeys_le fun c hc =>
      (h.occupied_of_mem_children c hc).size_le

/-- The height of a well-formed tree is logarithmic in its size (Cormen et al., Theorem 18.1). -/
theorem IsWF.height_le_log (h : IsWF t tr) : tr.height ≤ Nat.log t ((tr.size + 1) / 2) + 1 :=
  h.balanced.height_le_log h.two_le h.rootKeys_pos h.occupied_of_mem_children

end Cslib.DataStructure.BTree
